-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P56_classical_symmetries_monomial
-- name    : QAlgorithms.Papers.Independent.Information100.P56.classical_symmetries_monomial
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T12:15:19.064541+00:00
-- url     : https://prove2.me/theorems/9617a9a0-5f87-4893-ba71-a34a126f742f
-- title:
--   Section II B, unnumbered: classical input symmetries are monomial
-- statement:
--   Let $X$ be a finite nonempty preferred basis and let $U$ be unitary. If conjugation by $U$ maps the diagonal algebra onto itself, there exist a permutation $\pi$ and real phases $\theta(x)$ such that
--
--   $$U|x\rangle=e^{i\theta(x)}|\pi(x)\rangle.$$
--
--   For every diagonal matrix with entries $p(x)$, conjugation gives diagonal entries $p(\pi^{-1}(x))$; the phases therefore do not affect classical states. The diagonal-algebra hypothesis specifies the classical input model.
-- source:
--   From Symmetry to Secrecy: Covariant Classical--Quantum Wiretap Channels, arXiv:2610.03580v1, PDF p. 3, Section II B, unnumbered: classical input symmetries are monomial

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

namespace QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

/-- Section II B, p.3, Eq.(2): a unitary normalizing the diagonal algebra is monomial;
the phases have no effect on diagonal classical inputs. -/
theorem classical_symmetries_monomial
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (U : Matrix.unitaryGroup X ℂ)
    (hdiag : Set.image (fun D : Matrix X X ℂ => (U : Matrix X X ℂ) * D * (U : Matrix X X ℂ)ᴴ)
      (Set.range (Matrix.diagonal : (X → ℂ) → Matrix X X ℂ)) =
        Set.range (Matrix.diagonal : (X → ℂ) → Matrix X X ℂ)) :
    ∃ (pi : Equiv.Perm X) (theta : X → ℝ),
      (∀ i j, (U : Matrix X X ℂ) i j =
        if i = pi j then Complex.exp ((theta j : ℂ) * Complex.I) else 0) ∧
      (∀ p : X → ℂ,
        (U : Matrix X X ℂ) * Matrix.diagonal p * (U : Matrix X X ℂ)ᴴ =
          Matrix.diagonal (fun i => p (pi.symm i))) := by sorry

end QAlgorithms.Papers.Independent.Information100.P56

end
