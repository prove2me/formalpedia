-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P48_coherentSuperpositions
-- name    : QAlgorithms.Papers.Independent.Dependency50.P48.coherentSuperpositions
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T15:41:42.084872+00:00
-- url     : https://prove2.me/theorems/26d600cb-5b77-4ab5-bdeb-b7c3d89090df
-- title:
--   Coherent superpositions and the fraction of good Fourier choices
-- statement:
--   Let $N\ge1$ and let $(\chi_j)_{j=1}^N$ and $(\zeta_j)_{j=1}^N$ be orthonormal families in a common finite-dimensional complex Hilbert space. Suppose $\epsilon\ge0$ and all diagonal overlaps are real with $\langle\chi_j,\zeta_j\rangle\ge1-\epsilon$. For $s$ in a complete residue system modulo $N$, put
--
--   $$\widehat\chi_s=\frac1{\sqrt N}\sum_j e^{2\pi i js/N}\chi_j,\qquad \widehat\zeta_s=\frac1{\sqrt N}\sum_j e^{2\pi i js/N}\zeta_j.$$
--
--   There are a common frequency $s$ and a real phase $\theta$ for which $\langle\widehat\chi_s,e^{i\theta}\widehat\zeta_s\rangle$ is real and at least $1-\epsilon$. Moreover, if $0\le\epsilon\le1$, phases $\theta_s$ can be chosen so that
--
--   $$\#\{s:\langle\widehat\chi_s,e^{i\theta_s}\widehat\zeta_s\rangle\text{ is real and }\ge1-\sqrt\epsilon\}\ge(1-\sqrt\epsilon)N.$$
--
--   Thus a suitable coherent superposition preserves the overlap, and the displayed fraction controls the randomization used in Appendix D.
-- source:
--   The private classical capacity and quantum capacity of a quantum channel, arXiv:quant-ph/0304127v6, PDF p. 10, Lemma 4 and Moreover clause

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P48

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P48

open scoped BigOperators Matrix ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Information100.P22 (coherentInformation)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon)

open QAlgorithms.Papers.Independent.Information100.P67 (dilationPower)

attribute [local instance] Classical.propDecidable

variable {P Q E X H : Type*}

variable [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q]

variable [Fintype E] [DecidableEq E] [Fintype X] [DecidableEq X]

variable [Fintype H] [DecidableEq H]

/-- Lemma 4 and its 'Moreover' clause, PDF p.10. The complex inequalities
mean phase-aligned real overlaps. The fraction is 1-sqrt(eps), verified in the PDF.
The common Fourier frequency is chosen existentially. -/
theorem coherentSuperpositions [Nonempty H] {N : ℕ} (hN : 0 < N)
    (chi zeta : Fin N → EuclideanSpace ℂ H)
    (hchi : Orthonormal ℂ chi) (hzeta : Orthonormal ℂ zeta)
    (eps : ℝ) (heps : 0 ≤ eps)
    (hoverlap : ∀ j, RealOverlap (chi j) (zeta j) (1 - eps)) :
    (∃ (s : Fin N) (theta : ℝ),
      RealOverlap (phaseSuperposition chi (fourierPhase s))
        (phaseSuperposition zeta (fun j => fourierPhase s j + theta)) (1 - eps)) ∧
    (eps ≤ 1 → ∃ theta : Fin N → ℝ,
      (1 - Real.sqrt eps) * (N : ℝ) ≤
        ((Finset.univ.filter (fun s =>
          RealOverlap (phaseSuperposition chi (fourierPhase s))
            (phaseSuperposition zeta (fun j => fourierPhase s j + theta s))
            (1 - Real.sqrt eps))).card : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P48

end
