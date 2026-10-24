-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P15_remark3
-- name    : QAlgorithms.Papers.Independent.Support50.P15.remark3
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:37:09.110704+00:00
-- url     : https://prove2.me/theorems/77c63d17-a551-4323-832b-295001e6297f
-- title:
--   remark3
-- statement:
--   For $d\ge2$ let $M$ be the minimum in Eq. (6) and $\tau_d(u)=\operatorname{diag}(1-u,u/(d-1),\ldots,u/(d-1))$. For every $\Delta\in[-\log d,\log d]$ this minimum is attained. Its scalar minimizing pair $(s,r)$ is unique when $\Delta\ne0$. The witnesses obey
--
--   $$S(\tau_d(s))=H(s)+s\log(d-1),\qquad D(\tau_d(s)\|\tau_d(r))=D_2(s\|r).$$
--
--   The analogous entropy identity holds for $r$. Every ordered state pair of nonzero entropy difference $\Delta$ attains $M(\Delta,d)$ if and only if it is obtained from a minimizing witness pair by conjugating both states with the same unitary. At zero difference equality holds exactly for identical states. Thus uniqueness is simultaneous unitary equivalence of the ordered pair, and no uniqueness of the scalar pair is claimed at zero.
-- source:
--   Tight bound on relative entropy by entropy difference, arXiv:1304.0036v3, PDF p. 4, remark3

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- Remark 3, PDF p.4, with uniqueness proved pp.20--22. A common unitary acts on the ordered pair. -/
theorem remark3 (d : ℕ) (hd : 2 ≤ d) :
    (∀ delta ∈ Set.Icc (-Real.log d) (Real.log d), ∃ s r, minimizingPair d delta s r) ∧
    (∀ delta ∈ Set.Icc (-Real.log d) (Real.log d), delta ≠ 0 →
      ∃! sr : ℝ × ℝ, minimizingPair d delta sr.1 sr.2) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) (massLimit d), ∀ r ∈ Set.Icc (0 : ℝ) (massLimit d),
      entropy (family d s) = degenerateSpectrumEntropy d s ∧ entropy (family d r) = degenerateSpectrumEntropy d r ∧
      ∀ (ha : IsDensityMatrix (family d s)) (hb : IsDensityMatrix (family d r)),
        stateRelativeNats ⟨family d s, ha⟩ ⟨family d r, hb⟩ = binaryRelative s r) ∧
    (∀ (a b : EntropyState d) (delta : ℝ), delta ≠ 0 → difference a.val b.val = delta →
      (stateRelativeNats a b = tightBound d delta ↔
        ∃ s r, minimizingPair d delta s r ∧
          ∃ u : Matrix.unitaryGroup (Fin d) ℂ,
            a.val = (u : Matrix (Fin d) (Fin d) ℂ) * family d s * (u : Matrix (Fin d) (Fin d) ℂ)ᴴ ∧
            b.val = (u : Matrix (Fin d) (Fin d) ℂ) * family d r * (u : Matrix (Fin d) (Fin d) ℂ)ᴴ)) ∧
    (∀ a b : EntropyState d, difference a.val b.val = 0 →
      (stateRelativeNats a b = tightBound d 0 ↔ a = b)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P15

end
