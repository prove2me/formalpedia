-- Prove2me | Theorems.Thm_UnivESD_LogDet_kappa_eigen_bound
-- name    : UnivESD.LogDet.kappa_eigen_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T03:14:50.936993+00:00
-- url     : https://prove2.me/theorems/e7125ea0-3207-4dc6-a9a1-179919dab6a5
-- title:
--   §8, p. 2057 — a.s. $\frac1n\sum_{(1-\kappa)n<i\le n}\log\frac1{|\lambda_i|}\le O(\kappa\log\frac1\kappa)$ eventually
-- statement:
--   Let $A_n=M_n+X_n$ be as in Theorem 1.5, fix $z\in\mathbb C$, and let $\lambda_1,\dots,\lambda_n$ be the eigenvalues of $\tfrac1{\sqrt n}A_n-zI$, counted with multiplicity and ordered so that $|\lambda_1|\ge\dots\ge|\lambda_n|$. There is a constant $C$ such that for every fixed $0<\kappa<1/2$, almost surely, for all but finitely many $n$, all $\lambda_i$ are nonzero and
--   $$\frac1n\sum_{(1-\kappa)n<i\le n}\log\frac1{|\lambda_i|}\le C\,\kappa\log\frac1\kappa .$$
--
--   This bounds the logarithmic contribution of the eigenvalues of smallest modulus, which is what remains to control in the proof that convergence of the ESD (statement (i) of Theorem 1.15) implies convergence of the log-determinants (statement (ii)).
--
--   **Formalization Note** The conclusion holds for every enumeration `lam : Fin n → ℂ` of the root multiset of the characteristic polynomial with $|\lambda_i|$ non-increasing (the sum does not depend on how ties are ordered); the paper's $\lambda_i$ is `lam ⟨i-1, _⟩`. $C$ is chosen before $\kappa$, as in the singular-value bound. Nonvanishing of the $\lambda_i$ is part of the conclusion so that no term is Lean's junk $\log(1/0)=0$.
-- source:
--   Tao, Vu, Random matrices: Universality of ESDs and the circular law, Ann. Probab. 38 (2010), no. 5, p. 2057 (PDF 35), §8, proof of Theorem 1.15, (i) ⇒ (ii), second display

import Mathlib
import Definitions.Def_UnivESD_LogDet_Basic
import Definitions.Def_UnivESD_LogDet_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace UnivESD.LogDet

/-- §8, proof of (i) ⇒ (ii), p. 2057, second display. For `A_n` as in Theorem 1.5 and every
`z ∈ ℂ` there is a constant `C` such that for every fixed `0 < κ < 1/2`, almost surely, for all
but finitely many `n`: for every enumeration `λ_1, …, λ_n` of the eigenvalues of `A_n/√n − zI`
(with multiplicity) ordered so that `|λ_1| ≥ ⋯ ≥ |λ_n|`, all `λ_i ≠ 0` and
`(1/n) Σ_{(1−κ)n < i ≤ n} log(1/|λ_i|) ≤ C κ log(1/κ)`.
The paper's `λ_i` is `lam ⟨i - 1, _⟩`, so `(1−κ)n < i` is `⌊(1−κ)n⌋₊ < j.val + 1`. -/
theorem kappa_eigen_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (xs : ℕ → ℕ → Ω → ℂ) (hxs : IIDArray P xs)
    (M : (n : ℕ) → Matrix (Fin n) (Fin n) ℂ) (hM : HSBound M) (z : ℂ) :
    ∃ C : ℝ, ∀ κ : ℝ, 0 < κ → κ < 1 / 2 →
      ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ lam : Fin n → ℂ,
        Multiset.map lam Finset.univ.val = (shiftA M xs z n ω).charpoly.roots →
        Antitone (fun j => ‖lam j‖) →
          (∀ j, lam j ≠ 0) ∧
          (1 / (n : ℝ)) * ∑ j ∈ Finset.univ.filter
              (fun j : Fin n => ⌊(1 - κ) * (n : ℝ)⌋₊ < j.val + 1),
            Real.log (1 / ‖lam j‖) ≤ C * κ * Real.log (1 / κ) := by sorry

end UnivESD.LogDet
