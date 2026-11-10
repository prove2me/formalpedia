-- Prove2me | Theorems.Thm_RandomDimReduction_Channel_lemma_B_2
-- name    : RandomDimReduction.Channel.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T11:24:46.477213+00:00
-- url     : https://prove2.me/theorems/80377b6a-3ed5-496e-87ea-afc7cb15b95a
-- title:
--   Lemma B.2 — block diagonalization of intertwiners
-- statement:
--   Let $r_A,r_B$ be finite-dimensional unitary representations of a group $G$. Use a common finite family of pairwise inequivalent irreducible unitary representations $\rho_\lambda$ to write unitary decompositions $T_A,T_B$, with multiplicities $m_\lambda^A,m_\lambda^B$ that may be zero. If $M:A\to B$ satisfies $Mr_A(g)=r_B(g)M$ for every $g$, then there exist rectangular matrices $B_\lambda:\mathbb C^{m_\lambda^A}\to\mathbb C^{m_\lambda^B}$ such that
--   $$ T_BMT_A^\dagger=\bigoplus_\lambda B_\lambda\otimes I_{\rho_\lambda}. $$
--   All cross-label blocks are zero. This is the rectangular counterpart of the existing commutant theorem.
--
--   Differences from the source:
--   - generalization: G is compact and its finite-dimensional representations are unitary → any group with unitary matrix representations; reason: compactness is unnecessary once unitarity is given; every compact source instance is included
--   - encoding: the full irreducible label set, possibly infinite → a finite common label set of pairwise inequivalent nonzero irreducibles, allowing zero multiplicities; reason: only finitely many labels occur in the two finite-dimensional carriers; omitted labels have zero multiplicity in both
--   - encoding: orthogonal Hilbert-space decompositions T_A, T_B → unitary rectangular coordinate matrices satisfying the displayed representation identities; reason: orthonormal bases preserve every decomposition and intertwiner
-- source:
--   Angus Lowe, Xinyu Tan, Random dimension reduction and learning symmetric properties of quantum states, STOC 2027 submission #994 (October 2026), Lemma B.2, p.23. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/994.pdf

import Definitions.Def_RandomDimReduction_Channel_Representations

set_option autoImplicit false

noncomputable section
open Matrix MeasureTheory
open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise ENNReal

namespace RandomDimReduction.Channel
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma B.2, p.23, with the full setting on pp.22–23.
Any group is allowed because unitarity is already carried by the representations. -/
theorem lemma_B_2 {G L : Type} [Group G] [Fintype L] [DecidableEq L]
    (a b : ℕ) (mA mB dim : L → ℕ)
    (rA : G →* Matrix.unitaryGroup (Fin a) ℂ)
    (rB : G →* Matrix.unitaryGroup (Fin b) ℂ)
    (rho : ∀ l, G →* Matrix.unitaryGroup (Fin (dim l)) ℂ)
    (hirr : ∀ l, Irreducible (rho l))
    (hneq : ∀ l l', l ≠ l' → Inequivalent (rho l) (rho l'))
    (TA : RepDecomposition mA dim rA rho) (TB : RepDecomposition mB dim rB rho)
    (M : Matrix (Fin b) (Fin a) ℂ)
    (hM : ∀ g, M * (rA g : Op _) = (rB g : Op _) * M) :
    ∃ B : ∀ l, Matrix (Fin (mB l)) (Fin (mA l)) ℂ,
      TB.T * M * TA.Tᴴ =
        Matrix.blockDiagonal' (fun l => Matrix.kronecker (B l) (1 : Op (Fin (dim l)))) := by sorry

end RandomDimReduction.Channel
