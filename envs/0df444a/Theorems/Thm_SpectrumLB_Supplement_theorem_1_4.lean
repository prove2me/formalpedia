-- Prove2me | Theorems.Thm_SpectrumLB_Supplement_theorem_1_4
-- name    : SpectrumLB.Supplement.theorem_1_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T04:00:36.077016+00:00
-- url     : https://prove2.me/theorems/87bc1cb5-5ced-4277-8ce8-559def1ad8d5
-- title:
--   Theorem 1.4 — testing rank $\le\beta d$ against $\epsilon$-far needs $\Omega(d^{2-\gamma})$ copies
-- statement:
--   For all $\gamma>0$ and $0<\beta<1$ there exist a distance $\epsilon_{\gamma,\beta}>0$, a constant $c>0$ and a dimension $d_0$, none depending on $d$, such that for every $d\ge d_0$ and every $n$ the following holds. Suppose a two-outcome measurement of $n$ copies of an unknown $d$-dimensional state $\rho$
--
--   1. accepts with probability at least $2/3$ whenever $\operatorname{rank}\rho\le\beta d$, and
--   2. rejects with probability at least $2/3$ whenever $D_{\mathrm{tr}}(\rho,\sigma)\ge\epsilon_{\gamma,\beta}$ for every state $\sigma$ with $\operatorname{rank}\sigma\le\beta d$,
--
--   where $D_{\mathrm{tr}}(\rho,\sigma)=\frac12\|\rho-\sigma\|_1$. Then
--
--   $$
--   n\ \ge\ c\, d^{\,2-\gamma}.
--   $$
--
--   This improves the previous $\Omega(r)$ lower bound to nearly quadratic, and since rank testing with one-sided error is solvable with $\Theta(r^2)$ copies, it shows that one-sided and two-sided rank testing are almost equally hard.
--
--   **Formalization Note** The tester is an effect $0\preceq M\preceq I$ on $(\mathbb C^d)^{\otimes n}$ with the completeness and soundness conditions above (`RankTests`). $\Omega(\cdot)$ is $\exists c>0\,\exists d_0\,\forall d\ge d_0$ with $\epsilon$ chosen first, depending only on $\gamma,\beta$.
--
--   Differences from the source:
--   - encoding: Ω(d^{2−γ}) copies for a dimension-independent ε_{γ,β} → ∃ ε > 0, ∃ c > 0, ∃ d₀, ∀ d ≥ d₀, ∀ n, ∀ M, RankTests d n β ε M → c·d^(2−γ) ≤ n (real power), for every γ > 0 and every β ∈ (0,1); reason: standard reading of Ω with ε independent of d
--   - encoding: testing (with success probability 2/3, two-sided error) → an effect M (0 ⪯ M ⪯ 1) accepting each state of rank ≤ β·d with probability ≥ 2/3 and rejecting each state ε-far from all of them with probability ≥ 2/3; reason: every two-outcome measurement on n copies is an effect; 2/3 is Definition 1.1's convention, used by the proofs on pp.22–23; footnote 1 on p.3 fixes the two-sided reading
--   - encoding: rank at most β·d; ε-far in trace distance from all such states → (rank ρ : ℝ) ≤ β·d; ε ≤ traceDistance ρ σ for every density matrix σ with (rank σ : ℝ) ≤ β·d; reason: β·d is real; 'such states' are density matrices; D_tr = ½‖·‖₁ (Definition 2.3)
-- source:
--   Fanizza, O'Donnell, Wadhwa, Spectrum Estimation is Almost as Hard as Tomography, arXiv:2607.29680, Theorem 1.4, p. 3 (proof sketch p. 23)

import Mathlib
import Definitions.Def_SpectrumLB_Supplement_RankTests

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace SpectrumLB.Supplement

/-- **Theorem 1.4 (rank testing lower bound).**
Fanizza, O'Donnell, Wadhwa, *Spectrum Estimation is Almost as Hard as Tomography*, arXiv:2607.29680,
Theorem 1.4, p. 3: "For all γ > 0 and 0 < β < 1, there exists a dimension-independent ϵγ,β > 0 such
that testing whether a state has rank at most β·d or is ϵγ,β-far in trace distance from all such
states requires Ω(d^{2−γ}) copies of the state."

For all `γ > 0` and `0 < β < 1` there are `ε > 0`, `c > 0` and `d₀` such that for all `d ≥ d₀`, all
`n` and every two-outcome measurement `{M, 1 − M}` on `(ℂ^d)^{⊗n}` that accepts every state of rank
`≤ β·d` with probability `≥ 2/3` and rejects every state at trace distance `≥ ε` from all such states
with probability `≥ 2/3`, `n ≥ c · d^{2−γ}`.

**Formalization Note.** `Ω(·)` is `∃ c > 0, ∃ d₀, ∀ d ≥ d₀` with `ε` chosen first and depending only
on `γ, β` ("dimension-independent"). Every `β ∈ (0, 1)` and every `d ≥ d₀` are covered. The tester
has two-sided error (`RankTests`). The exponent is a real power. -/
theorem theorem_1_4 :
    ∀ γ : ℝ, 0 < γ → ∀ β : ℝ, 0 < β → β < 1 →
      ∃ ε : ℝ, 0 < ε ∧ ∃ c : ℝ, 0 < c ∧ ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ n : ℕ,
        ∀ M : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ,
          RankTests d n β ε M →
            c * (d : ℝ) ^ ((2 : ℝ) - γ) ≤ n := by sorry

end SpectrumLB.Supplement
