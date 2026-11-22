-- Prove2me | Theorems.Thm_SamplingLLL_Supplement_theorem_5_4
-- name    : SamplingLLL.Supplement.theorem_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T05:00:01.221727+00:00
-- url     : https://prove2.me/theorems/1817ae59-09bb-4dd7-8541-13affe0249e2
-- title:
--   Theorem 5.4, pp.16–17 — Finite-Range Theorem: deterministic counting and near-perfect sampling from (FR) through size $L$
-- statement:
--   Let an atomic product-space CSP have $m\ge1$ constraints, scopes of size at most $k$, and dependency graph of maximum degree at most $D$; put $d=D+1$. Suppose that, for some rational $p_0>0$ and integer $L\ge2$,
--   $$
--   128\,d\,p_0\le1,\qquad\lambda\Bigl(\bigcap_{b\in T}\mathrm{Bad}_b\Bigr)\le p_0^{|T|} \tag{FR}
--   $$
--   for every compatible family $T$ with $|T|\le L$ that is connected in $H$. Then:
--
--   1. $Z>0$;
--   2. the deterministic estimate $\hat Z$ satisfies $|\log(\hat Z/Z)|\le16\,m\,p_0\,2^{-L}$;
--   3. one sampling attempt fails with probability at most $\delta_L=8\,m\,p_0\,16^{-(L-1)}$;
--   4. its successful-output subprobability measure is dominated by $\mu$: for every set $U$ of assignments, one attempt returns a member of $U$ with probability at most $\mu(U)$;
--   5. if $\delta_L<1$, restarting the whole attempt after failure returns a satisfying assignment whose law is within $\delta_L$ of $\mu$ in total variation;
--   6. counting has deterministic bit complexity, and one sampling attempt expected bit complexity, at most
--   $$
--   C\,(N+L+\ell(p_0)+1)^{e}\,2^{C\,d\,L}
--   $$
--   with absolute constants $C$, $e$, where $N$ is the input length (including the encoding of $\lambda$) and $\ell(p_0)$ that of $p_0$; restarting multiplies the expected bit complexity of one attempt by at most $1/(1-\delta_L)$.
--
--   The theorem needs the local-lemma condition only for connected families up to a finite size, at the price of a small explicit error.
--
--   **Formalization Note** The procedures are `frCount`, `frAttempt` and `frRestart` of Appendix D. A failure is the output `none`. The counter draws no random bits and the statement bounds every outcome, so $\hat Z$ is a number and its cost a worst-case bound; $\hat Z>0$ is part of clause 2. The restart clause is stated as $(1-\delta_L)\,\mathbb E[\text{restart}]\le\mathbb E[\text{attempt}]$. The scope bound $k$ is a hypothesis as printed; it does not occur in the conclusions.
--
--   Differences from the source:
--   - reading: "a deterministic estimate $\hat Z$", "one sampling attempt", "restarting the whole attempt" → the clauses are stated for the explicit procedures `frCount` (which draws no random bits), `frAttempt` and `frRestart` of Appendix D, with no existential quantifier over programs; reason: the base mission's `Proc` has no machine model, so an existential over programs would make every running-time clause vacuous; this is the convention of the published Theorem 2.6
--   - reading: "at most $\mathrm{poly}(N+L+\ell(p_0))\,2^{O(dL)}$" → at most $C(N+L+\ell(p_0)+1)^e2^{CdL}$ with absolute $C$, $e$ chosen before the instance; reason: the polynomial and the constant of the $O(\cdot)$ are not given; absolute constants are the strongest reading
--   - encoding: $|\log(\hat Z/Z)|\le16mp_02^{-L}$ → the same bound together with $\hat Z>0$; reason: Lean's logarithm of a non-positive number is $0$, so positivity is stated; the printed bound presupposes it
--   - encoding: "restarting multiplies the latter by at most $1/(1-\delta_L)$" → $(1-\delta_L)\,\mathbb E[\text{ticks of restart}]\le\mathbb E[\text{ticks of one attempt}]$, under $\delta_L<1$; reason: the same inequality without a division in extended nonnegative reals
--   - encoding: the attempt and the restarted sampler are procedures that stop → termination with probability one of the counter, of one attempt, and (when $\delta_L<1$) of the restarted sampler are stated conclusions; reason: needed for the stated probabilities and laws to refer to probability measures
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Theorem 5.4, pp.16–17; proof in Appendix D.1–D.5, pp.39–45

import Mathlib
import Definitions.Def_SamplingLLL_Supplement_frData

set_option autoImplicit false

open scoped ENNReal

namespace SamplingLLL.Supplement

open Proc

/-- Theorem 5.4 (Finite-Range Theorem), pp.16–17. Let an atomic product-space CSP have `m ≥ 1` constraints,
scopes of size at most `k`, and dependency graph of maximum degree at most `D`; put `d = D + 1`. Suppose that
for a rational `p₀ > 0` and an integer `L ≥ 2`, `128 d p₀ ≤ 1` and (FR)
`λ(⋂_{b∈T} Bad_b) ≤ p₀^{|T|}` for every compatible family `T` with `|T| ≤ L` connected in `H`. Then:

1. `Z > 0`;
2. the deterministic estimate `Ẑ` of D.5 satisfies `|log(Ẑ/Z)| ≤ 16 m p₀ 2^{−L}`;
3. one sampling attempt fails with probability at most `δ_L = 8 m p₀ 16^{−(L−1)}`;
4. its successful-output subprobability is dominated by `μ`: for every set `U` of assignments, the attempt
   returns a member of `U` with probability at most `μ(U)`;
5. if `δ_L < 1`, restarting the whole attempt after failure returns an assignment whose law is within `δ_L`
   of `μ` in total variation;

and counting has deterministic bit complexity, and one attempt expected bit complexity, at most
`C (N + L + ℓ(p₀) + 1)^e 2^{C d L}` with absolute `C`, `e`; restarting multiplies the expected bit
complexity of one attempt by at most `1/(1 − δ_L)`.

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), Theorem 5.4, pp.16–17; proof in
Appendix D.1–D.5, pp.39–45.

**Formalization Note.** The clauses are about the explicit procedures `frCount`, `frAttempt` and
`frRestart` of Appendix D. A failure (abort) is the output `none`, propagated to the top of the attempt.
`Ẑ` is computed by a procedure that draws no random bits, and the statement bounds every outcome, so it is
deterministic and its cost is a worst-case bound. `N = frInputSize` is the base input length, which
includes the encoding of `λ`; `ℓ(p₀) = bits p₀`. "`poly(N + L + ℓ(p₀)) 2^{O(dL)}`" is
`C (N + L + ℓ(p₀) + 1)^e 2^{C d L}`. The restart clause is stated as `(1 − δ_L) E[restart] ≤ E[attempt]`. -/
theorem theorem_5_4 : ∃ C e : ℕ, ∀ {n m : ℕ} (I : AtomicCSP n m) (k D L : ℕ) (p₀ : ℚ),
    1 ≤ m → (∀ a, (I.vbl a).card ≤ k) → (∀ a, (I.H.neighborFinset a).card ≤ D) →
    0 < p₀ → 2 ≤ L → 128 * ((D : ℚ) + 1) * p₀ ≤ 1 →
    (∀ T : Finset (Fin m), T.card ≤ L → I.compat T → (I.H.induce (T : Set (Fin m))).Connected →
      I.jointBad T ≤ p₀ ^ T.card) →
    let δL : ℝ := 8 * m * (p₀ : ℝ) * (1 / 16 : ℝ) ^ (L - 1)
    let Bd : ℕ := C * (frInputSize I + L + bits p₀ + 1) ^ e * 2 ^ (C * (D + 1) * L)
    0 < I.toCSP.Z Finset.univ ∧
    mass (frCount I p₀ L) = 1 ∧
    (∀ r, frCount I p₀ L r ≠ 0 →
      0 < r.1 ∧
      |Real.log ((r.1 : ℝ) / (I.toCSP.Z Finset.univ : ℝ))| ≤ 16 * m * (p₀ : ℝ) * (1 / 2 : ℝ) ^ L ∧
      r.2.1 ≤ Bd) ∧
    mass (frAttempt I p₀ L) = 1 ∧
    probOf (frAttempt I p₀ L) (fun o => o = none) ≤ ENNReal.ofReal δL ∧
    (∀ U : Finset I.toCSP.Config,
      probOf (frAttempt I p₀ L) (fun o => ∃ x ∈ U, o = some x) ≤
        ENNReal.ofReal (∑ x ∈ U, ((I.toCSP.mu Finset.univ x : ℚ) : ℝ))) ∧
    expTicks (frAttempt I p₀ L) ≤ (Bd : ℝ≥0∞) ∧
    (δL < 1 →
      mass (frRestart I p₀ L) = 1 ∧
      SupportedOn (frRestart I p₀ L) (fun x => I.toCSP.sat Finset.univ x = true) ∧
      tvDist (frRestart I p₀ L) (fun x => ((I.toCSP.mu Finset.univ x : ℚ) : ℝ)) ≤ δL ∧
      ENNReal.ofReal (1 - δL) * expTicks (frRestart I p₀ L) ≤ expTicks (frAttempt I p₀ L)) := by sorry

end SamplingLLL.Supplement
