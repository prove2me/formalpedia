-- Prove2me | Theorems.Thm_RelatedSchedFPTAS796_Main_lemma_4_4
-- name    : RelatedSchedFPTAS796.Main.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:14:45.352696+00:00
-- url     : https://prove2.me/theorems/e1c20368-545a-48a7-b4c3-07a3bfffed2a
-- title:
--   Lemma 4.4 — the exact sumset of Algorithm 1's leaves contains an $\tilde O(\kappa)$-approximation of any fixed target profile w.p. $\ge1-q$
-- statement:
--   Let $(J,\kappa,q)$ be an admissible partial-profile instance of dimension $d\ge1$ at accuracy $\varepsilon=2^{-\ell}$, and run Algorithm 1 with a complete-profile procedure that meets Definition 3.1 on its recursive calls. Write
--   $$S_\ell=\bigcup_{r=1}^{R}\big(S^{(r)}_{\ell,1}+\dots+S^{(r)}_{\ell,G}\big),\qquad S=S_1+\dots+S_K$$
--   for the exact set expressions built from the leaves. For any fixed $s\in\mathcal S(J,[\kappa/\varepsilon,(2d+1)\kappa/(2d\varepsilon)))$, with probability at least $1-q$ the set $S$ contains a vector $\tilde s$ with
--   $$|\tilde s_i-s_i|\ \le\ C\,\kappa_i\,(\log_2(|J|+2)\log_2(2/\varepsilon)\log_2(2/q))^c\qquad\text{for every } i,$$
--   an additive error $\tilde O(\kappa)$.
--
--   Precisely: for every $d\ge1$ and every admissibility constant $a$ there is a constant $a'$ such that for all error constants $C_1,c_1$ of the procedure there are $C,c$ with the following property. If, for every $\ell$, every number $k\le d$ of machines and every $a'$-admissible complete-profile instance $(B,t,q_0)$ with $B\ne\emptyset$, the procedure's output fails to approximate $\mathcal P(B,[0,t])$ with additive error $C_1\varepsilon t_i(\log_2(|B|+2)\log_2(2/\varepsilon)\log_2(2/q_0))^{c_1}$ with probability at most $q_0$, then the conclusion above holds for every $a$-admissible instance and every fixed target profile $s$.
--
--   This is the correctness of the random leaf construction; together with Lemma 5.8 and a union bound over the target profiles it yields Lemma 5.9.
--
--   **Formalization Note** Algorithm 1 is the definition `algorithm1`, a line-by-line transcription of p.11 with independent randomness for all partitions and calls; $\pi$ filters with the procedure's error bound `cpError`, the "known coordinatewise additive error bounds" of p.11.
--
--   Differences from the source:
--   - reading: Algorithm 1 with its recursive CompleteProfile calls, "the call's known coordinatewise additive error bounds" → Algorithm 1 as a probability distribution, parameterized by a procedure whose outputs meet Definition 3.1 with error $C_1\varepsilon t_i\,\mathrm{polylog}^{c_1}$ on $a'$-admissible instances with at most $d$ machines; $\pi$ uses that bound; reason: the lemma is a statement about the exact set expressions given that every call meets Definition 3.1; the error constants are universally quantified
--   - encoding: $1/\varepsilon$ a power of two (p.7, the convention of §§3–5) → $\varepsilon=2^{-\ell}$ with $\ell\ge1$, given as the word $\ell$; reason: the paper's own convention for these sections; $\varepsilon<1$
--   - reading: "$O(1/\varepsilon)$ jobs", "$t_i=O(1/\varepsilon^2)$", "$\kappa_d=O(1/\varepsilon)$" → for every constant $a$: $|J|\le a/\varepsilon$, $t_i\le a/\varepsilon^2$, $\kappa_d\le a/\varepsilon$, with the program and its constants depending on $a$; reason: the strongest reading of the hidden constants; it is what the reductions of Appendix C produce
--   - encoding: $\tilde O(X)$, suppressing factors polynomial in $\log(|J|+2)$, $\log(2/\varepsilon)$, $\log(2/q)$, constants depending on the dimension → $C\cdot X\cdot(\log_2(|J|+2)\log_2(2/\varepsilon)\log_2(2/q))^c$ with $C,c\in\mathbb N$ fixed before the instance; reason: the paper's definition of $\tilde O$ (p.7)
-- source:
--   Lin Chen, Tingwei Hu, Jiayi Lian, Yuchen Mao, Guochuan Zhang, Faster Approximation Schemes for Scheduling on Related Machines, STOC 2027 submission #796 (October 2026), source.pdf SHA-256 5d7d0135eed9cbe942c80598e2bb07d8c56ab67aec0d6e8486a067237654f7f3, p.12, Lemma 4.4 (proof p.12); Algorithm 1 and its parameters pp.10–11

import Mathlib
import Definitions.Def_RelatedSchedFPTAS796_Main_Model
import Definitions.Def_RelatedSchedFPTAS796_Main_Machine
import Definitions.Def_RelatedSchedFPTAS796_Main_Problems
import Definitions.Def_RelatedSchedFPTAS796_Main_Algorithm1

set_option autoImplicit false

namespace RelatedSchedFPTAS796.Main

/-- **Lemma 4.4**, p.12 (proof p.12). Write `S_ℓ = ⋃_{r=1}^{R}(S^{(r)}_{ℓ,1} + ⋯ + S^{(r)}_{ℓ,G})` and
`S = S_1 + ⋯ + S_K` for the exact set expressions of Algorithm 1 (`algorithm1`). For any fixed
`s ∈ 𝒮(J, [κ/ε, (2d+1)κ/(2dε)))`, with probability at least `1 − q`, `S` contains a vector `s̃`
approximating `s` with additive error `Õ(κ)`.

Here `(J, κ, q)` is an `a`-admissible partial-profile instance of dimension `d ≥ 1` and every
`CompleteProfile` call of the algorithm meets Definition 3.1: on every `a'`-admissible
complete-profile instance on `k ≤ d` machines with a nonempty job set, its output fails to
approximate `𝒫(B, [0, t])` with additive error `C₁·ε·t·polylog^{c₁}` (`cpError`, the bound used by
`π`) with probability at most `q₀`. The constant `a'` depends on `(d, a)`; the error constants
`C, c` of the conclusion depend on `(d, a, C₁, c₁)`; `Õ(κ)` is `C·κ_i·(log₂(|J|+2)·log₂(2/ε)·
log₂(2/q))^c` in coordinate `i`. -/
theorem lemma_4_4 (d : ℕ) (hd : 1 ≤ d) (a : ℕ) : ∃ a' : ℕ, ∀ C₁ c₁ : ℕ, ∃ C c : ℕ,
    ∀ cp : CPProcedure,
      (∀ (ℓ k : ℕ) (B : Multiset ℕ) (t : Fin k → ℚ) (q₀ : ℚ), 1 ≤ k → k ≤ d → B ≠ 0 →
        IsAdmissibleComplete a' ℓ B.toList t q₀ →
        (cp ℓ k B t q₀).toOuterMeasure
            {T | ¬ ApproxAdd (workProfiles k (jobsOf B.toList))
              ((fun x i => (x i : ℝ)) '' (T : Set (Fin k → ℚ))) (Set.Icc 0 (fun i => (t i : ℝ)))
              (cpError ℓ C₁ c₁ B t q₀)} ≤ ENNReal.ofReal q₀) →
      ∀ (ℓ : ℕ) (J : List ℕ) (κ : Fin d → ℚ) (q : ℚ), IsAdmissiblePartial a ℓ J κ q →
        ∀ s ∈ partialProfiles d (jobsOf J) ∩ partialBox ℓ κ,
          ENNReal.ofReal (1 - q) ≤ (algorithm1 cp ℓ C₁ c₁ J κ q).toOuterMeasure
            {S | ∃ s' ∈ S, ∀ i, |(s' i : ℝ) - s i| ≤
              C * (κ i : ℝ) * polylog3 J.length (epsOf ℓ) q c} := by sorry

end RelatedSchedFPTAS796.Main
