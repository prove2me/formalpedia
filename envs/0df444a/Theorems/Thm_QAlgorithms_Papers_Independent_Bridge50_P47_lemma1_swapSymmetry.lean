-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P47_lemma1_swapSymmetry
-- name    : QAlgorithms.Papers.Independent.Bridge50.P47.lemma1_swapSymmetry
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:44:23.96913+00:00
-- url     : https://prove2.me/theorems/d3a530ac-db21-47e4-ad84-1062e0800a55
-- title:
--   Lemma 1: swap symmetry of a degradable dilation
-- statement:
--   Let $\mathcal N:\mathcal L(A')\to\mathcal L(B)$ be a degradable channel on nonzero finite dimensional complex systems, and fix its Stinespring isometry $U:A'\to B\otimes E$. The complementary channel is the partial trace over $B$ of this same dilation. There are a nonzero finite system $F$, an isometric dilation $V:B\to F\otimes E'$ of a CPTP degrading map to that complement, and a unitary $X$ on $F$ with $X^2=I_F$, such that
--
--   $$
--   (X_F\otimes\operatorname{SWAP}_{EE'})(V\otimes I_E)U=(V\otimes I_E)U.
--   $$
--
--   Here $E'$ is an identified copy of $E$ and tensor factors are permuted to the displayed order. Consequently, for every finite reference $R$ and unit vector $\phi\in R\otimes A'$, the vector $\psi=(I_R\otimes(V\otimes I_E)U)\phi$ satisfies $(I_R\otimes X_F\otimes\operatorname{SWAP}_{EE'})\psi=\psi$. The possibly enlarged degrading environment supplies a symmetry of the full dilation, beyond equality of the two environment marginals.
-- source:
--   "Pretty strong" converse for the quantum capacity of degradable channels, arXiv:1301.4927v3, PDF p. 4, Lemma 1: swap symmetry of a degradable dilation

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P47

noncomputable section

open scoped BigOperators ComplexConjugate Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Bridge50.P47

open QAlgorithms.Papers.Independent.Information100

variable {A B E F R I O : Type*}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

variable [Fintype R] [DecidableEq R] [Fintype I] [DecidableEq I]

variable [Fintype O] [DecidableEq O]

/-- Lemma 1, PDF p.4: a genuinely degrading dilation has swap symmetry
up to a unitary involution on its possibly enlarged environment. -/
theorem lemma1_swapSymmetry [Nonempty A] [Nonempty B] [Nonempty E]
    (U : Matrix (B × E) A ℂ) (hU : P67.IsDegradable U) :
    ∃ f : ℕ, 0 < f ∧ ∃ V : Matrix (Fin f × E) B ℂ,
      IsDegradingDilation U V ∧ ∃ X : Matrix.unitaryGroup (Fin f) ℂ,
        X * X = 1 ∧
        Matrix.kronecker (X : Matrix (Fin f) (Fin f) ℂ)
          (P67.environmentSwap (E := E)) * P67.symmetricDilation U V =
          P67.symmetricDilation U V ∧
        ∀ r : ℕ, ∀ phi : EuclideanSpace ℂ (Fin r × A), ‖phi‖ = 1 →
          WithLp.toLp 2 ((Matrix.kronecker
            (Matrix.kronecker (1 : Matrix (Fin r) (Fin r) ℂ)
              (X : Matrix (Fin f) (Fin f) ℂ))
            (P67.environmentSwap (E := E))).mulVec (testKet U V phi)) =
            testKet U V phi := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P47

end
