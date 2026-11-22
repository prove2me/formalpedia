-- Prove2me | Theorems.Thm_SamplingLLL_Supplement_theorem_F_6
-- name    : SamplingLLL.Supplement.theorem_F_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-22T05:01:14.539652+00:00
-- url     : https://prove2.me/theorems/13b311b9-a41e-4dcb-9218-4ab58c13880c
-- title:
--   Theorem F.6, p.55 — deterministic algorithmic theorem for $k$-CNF with a sparse high-degree core under (D1)–(D4)
-- statement:
--   Fix integers $k\ge4$, $\Delta\ge1$, constants $a_{\mathrm{blk}}>0$, $0<\delta\le1$ and a positive integer $\beta$, put $N_0=n+m+2$, $d=1+k\Delta$, $p=2^{-k+3}$, $K_0=256$, and suppose
--   $$
--   K_0\,d\,p\,e^2\le1/4 . \tag{55}
--   $$
--   Let $F$ be a formula of $m\ge1$ labelled clauses on $n$ Boolean variables with exactly $k$ distinct variables in each clause, and let the decomposition $F_U$, $C_{\mathrm{res}}$ given by a set $U$ of variables satisfy (D1)–(D3) and
--   $$
--   \max_{1\le i\le s_B}T_i(F;L_0)\le N_0^{\beta}. \tag{D4}
--   $$
--   Then there are constants depending only on $k,\Delta,a_{\mathrm{blk}},\delta,\beta$ such that, for every choice of literal signs and every rational $\varepsilon\in(0,1)$:
--
--   1. the formula is satisfiable;
--   2. the FPRAS terminates and outputs a number within relative error $\varepsilon$ of the number of satisfying assignments with probability at least $3/4$;
--   3. the sampler terminates, every output satisfies all clauses, and its law is within total variation distance $\varepsilon$ of the uniform law on satisfying assignments;
--   4. the expected running time of both is at most $C\,((N_0+\ell(\varepsilon))/\varepsilon)^{e}$.
--
--   For $s_B=0$ condition (D4) is vacuous. No probability distribution on the input is assumed: this is a deterministic promise theorem with scope-only hypotheses, and it is the engine of Theorem 2.18.
--
--   **Formalization Note** The hypotheses are `Core.D1`–`Core.D4`, with the connection sum `Core.T` of (62). The algorithms are `Core.coreCount` and `Core.coreSample`: the lazy block heat-bath chain on the core with residual counts from Theorem 5.4, the residual sampler, and counting by packet insertion. The existential constants are $C_{\mathrm{core}}$ (the constant of (67)), the cap polynomial $(K,e)$ of p.57, and $C$.
--
--   Differences from the source:
--   - reading: "the formula … has an FPRAS, and, for every $\varepsilon\in(0,1)$, admits a sampler" → the clauses are stated for the explicit procedures `coreCount` and `coreSample` of the proof (pp.55–57), with no existential quantifier over programs; reason: the base mission's `Proc` has no machine model, so an existential over programs would make every running-time clause vacuous; this is the convention of the published Theorem 2.6
--   - reading: the proof uses $T_{\mathrm{core}}=O(e\,s_BN_0^\beta[n+\log(1/\varepsilon)])$ (67) and a cap at "sixteen times the proved polynomial upper bound" (p.57) without giving the constants → $T_{\mathrm{core}}=C_{\mathrm{core}}s_BN_0^\beta(n+\lceil\log_2\lceil1/\varepsilon_0\rceil\rceil)$ and a cap $K\lceil(N_0+\ell(\varepsilon))/\varepsilon\rceil^e$, with $C_{\mathrm{core}},K,e$ quantified existentially after $k,\Delta,a_{\mathrm{blk}},\delta,\beta$ and before the formula; reason: they are constants of the paper's own algorithm and may depend only on the fixed parameters, like the exponent
--   - reading: details the proof leaves open: the cutoff "requested by Theorem 5.4", the block chosen by a heat-bath update, the initial core state, and the irrational $q_{\min}=N_0^{-4pa_{\mathrm{blk}}}$ used in $\tau$ and $M_B$ → the cutoff of p.48 for the residual formula; a uniformly random block with holding probability $1/2$; the first element of each $\Omega_B$; and the rational $\tilde q=2^{-\lceil4pa_{\mathrm{blk}}\rceil\lceil\log_2N_0\rceil}\le q_{\min}$; reason: each is the paper's own choice elsewhere (p.48), the standard meaning of the lazy heat-bath chain to which the spectral-gap bound of p.56 refers, allowed explicitly ("from any core state"), or a rational lower bound that only increases the printed sample count and accuracy
--   - reading: syntactic codes: "Missing positions or clone indices give an invalid code", "Invalid instructions stop the affected traversal", "an old-root vertex and corner" → positions range over $k$ and clones over $\Delta$ indices on every edge; an invalid instruction stops the traversal of that edge and of the subtree below it; the (vertex, corner) pairs of a tree on $K\ge2$ vertices number $2(K-1)$; reason: the literal reading of F.3.1 and F.4: "at most $d$ instructions per edge", codes "listed before testing whether they represent valid terms", and a corner is "a gap in the cyclic order of the half-edges incident with a vertex"
--   - reading: "Their expected running time is polynomial in $N_0/\varepsilon$, with exponent depending only on $k,\Delta,a_{\mathrm{blk}},\delta,\beta$" → expected ticks at most $C((N_0+\ell(\varepsilon))/\varepsilon)^e$ with $C,e$ depending only on the five parameters, for $\varepsilon$ rational; reason: the accuracy is a rational given in binary and reading it is charged; the two bounds agree when $\varepsilon$ is written with $O(\log(1/\varepsilon))$ bits
--   - encoding: "has an FPRAS … succeeds with probability at least $3/4$"; "a sampler supported on satisfying assignments" → both procedures terminate with probability one; relative error $\varepsilon$ with probability at least $3/4$; every outcome of positive probability satisfies all clauses; reason: the usual meaning; termination is needed for the output laws to be probability laws
-- source:
--   Achlioptas, Counting and Sampling by Local Repair: From the Lovász Local Lemma to Random k-SAT, STOC 2027 submission (manuscript sha256 7a943167…), Theorem F.6, p.55; (55), (D1)–(D3), (56), pp.49–50; (62), p.54; proof on pp.55–57

import Mathlib
import Definitions.Def_SamplingLLL_Supplement_coreSample

set_option autoImplicit false

open scoped ENNReal

namespace SamplingLLL.Supplement

open Proc

/-- Theorem F.6 (the deterministic algorithmic theorem), p.55. Fix integers `k ≥ 4`, `∆ ≥ 1`, constants
`a_blk > 0`, `0 < δ ≤ 1` and a positive integer `β`, and suppose (55): `K₀ d p e² ≤ 1/4` with `K₀ = 256`,
`d = 1 + k∆`, `p = 2^{−k+3}`. Let `F` be a formula of `m ≥ 1` labelled clauses on `n` Boolean variables with
exactly `k` distinct variables in each clause, and let the decomposition `F_U`, `C_res` given by a set `U` of
variables satisfy (D1)–(D3) and (D4): `max_i T_i(F; L₀) ≤ N₀^β`. Then for every choice of literal signs and
every rational `ε ∈ (0,1)`:

1. the formula is satisfiable;
2. the FPRAS terminates and its output is within relative error `ε` of the number of satisfying assignments
   with probability at least `3/4`;
3. the sampler terminates, every output satisfies all clauses, and its law is within total variation
   distance `ε` of the uniform law on satisfying assignments;
4. both run in expected time at most `C ((N₀ + ℓ(ε))/ε)^e`, where `C` and `e` depend only on
   `k, ∆, a_blk, δ, β`.

Source: Achlioptas, STOC 2027 submission (manuscript sha256 7a943167…), Theorem F.6, p.55; hypotheses
(55), (D1)–(D3) on pp.49–50, (62) and (D4) on pp.54–55; proof on pp.55–57.

**Formalization Note.** The clauses are about the explicit procedures `Core.coreCount` and
`Core.coreSample` of the proof (block heat bath on the core with residual counts from Theorem 5.4, then the
residual sampler; counting by packet insertion), not about programs chosen by `∃`, since `Proc` has no
machine. Three constants of the algorithm are not explicit in the paper and are quantified existentially
after the fixed parameters: the constant `C_core` of `T_core = O(·)` in (67), and the polynomial `K ·^e` of
the work cap of p.57. The accuracy `ε` is a rational given in binary and reading it is charged, so the time
bound is in `(N₀ + bits ε)/ε` (the paper's `N₀/ε` when `ε` is written with `O(log(1/ε))` bits). The
hypotheses do not mention the signs. For `s_B = 0`, (D4) quantifies over no block. -/
theorem theorem_F_6 : ∀ (k Δ β : ℕ) (ablk δ : ℝ), 4 ≤ k → 1 ≤ Δ → 0 < ablk → 0 < δ → δ ≤ 1 → 1 ≤ β →
    256 * (1 + (k : ℝ) * Δ) * (8 / 2 ^ k) * Real.exp 1 ^ 2 ≤ 1 / 4 →
    ∃ Ccore K e C : ℕ, ∀ {n m : ℕ} (F : Core n m), 1 ≤ m → (∀ c, (F.scope c).card = k) →
      F.D1 Δ → F.D2 ablk → F.D3 k δ → F.D4 k Δ β →
      ∀ (sgn : Fin m → Fin n → Bool) (ε : ℚ), 0 < ε → ε < 1 →
        let I := kcnf F.scope sgn
        let T : ℝ := C * (((F.N0 : ℝ) + bits ε) / ε) ^ e
        (∃ x, I.toCSP.sat Finset.univ x = true) ∧
        mass (F.coreCount sgn k ablk β Ccore K e ε) = 1 ∧
        (3 / 4 : ℝ≥0∞) ≤ probOf (F.coreCount sgn k ablk β Ccore K e ε) (fun Nh =>
          (1 - ε) * (numSat I : ℚ) ≤ Nh ∧ Nh ≤ (1 + ε) * (numSat I : ℚ)) ∧
        expTicks (F.coreCount sgn k ablk β Ccore K e ε) ≤ ENNReal.ofReal T ∧
        mass (F.coreSample sgn k β Ccore Finset.univ ε) = 1 ∧
        SupportedOn (F.coreSample sgn k β Ccore Finset.univ ε)
          (fun x => I.toCSP.sat Finset.univ x = true) ∧
        tvDist (F.coreSample sgn k β Ccore Finset.univ ε)
          (fun x => if I.toCSP.sat Finset.univ x = true then (numSat I : ℝ)⁻¹ else 0) ≤ ε ∧
        expTicks (F.coreSample sgn k β Ccore Finset.univ ε) ≤ ENNReal.ofReal T := by sorry

end SamplingLLL.Supplement
