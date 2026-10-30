-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P01_infinitesimal_intertwiner
-- name    : QAlgorithms.Papers.Independent.Extend50.P01.infinitesimal_intertwiner
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:37:05.177476+00:00
-- url     : https://prove2.me/theorems/73481505-ee97-409d-8a4c-117152687bae
-- title:
--   §II general case, Eqs.(40)–(44): infinitesimal intertwining suffices along flows
-- statement:
--   Let $\mathcal E$ be a real-linear map from $\mathbb R^d$ into traceless Hermitian operators on $n$ qubits. Let $G$ be a real data-space endomorphism and $H$ a traceless skew-Hermitian matrix. Suppose $\mathcal E(Gx)=[H,\mathcal E(x)]$ for every $x$. Then, for every real $t$ and $x$,
--   $$\mathcal E(e^{tG}x)=e^{tH}\mathcal E(x)e^{-tH},\qquad e^{-i\mathcal E(e^{tG}x)}=e^{tH}e^{-i\mathcal E(x)}e^{-tH}.$$
--   This is the one-parameter infinitesimal intertwining criterion. Hermitian physics operators are explicitly distinguished from skew-Hermitian Lie generators; no claim about integrating arbitrary global group elements is needed.
-- source:
--   Exploiting symmetry in variational quantum machine learning, arXiv:2205.06217v1, PDF p. 7, §II general case, Eqs.(40)–(44): infinitesimal intertwining suffices along flows

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P01

noncomputable section

open scoped Matrix Kronecker ComplexConjugate Matrix.Norms.L2Operator Manifold ContDiff

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P01

attribute [local instance] Classical.propDecidable Classical.decEq

-- PDF pp.3,8: reuse the accepted operator type, exp(-itH), and A X A†.
-- Notation specializes the imported interfaces without introducing duplicate declarations.

local notation "Op" => (fun n : ℕ => QAlgorithms.Papers.Independent.Information100.P21.Op (Qubits n))

local notation "evolve" => QAlgorithms.Papers.Independent.Information100.P32.evolution

local notation "conjugate" => QAlgorithms.conjSuperop

-- PDF pp.3,10–11: the imported quadratic form is Re(psi† A psi).

local notation "expectation" => QAlgorithms.Papers.Independent.Information100.P21.quad

-- PDF pp.5,16–19: accepted active-wire operator, with identities on all spectators.

local notation "onWire" => QAlgorithms.Papers.Independent.Advance50.P49.onWire

-- PDF p.5: the imported phase-free Pauli tensor uses 0=I,1=X,2=Y,3=Z.

local notation "pauliWord" => QAlgorithms.Papers.Independent.Gap48.P33.pauliWord

/-- PDF p.7, Eqs.(40)–(44): Hermitian physics embedding and skew-Hermitian Lie generator.
The conclusion is along flows only; no global integration assertion is made. -/
theorem infinitesimal_intertwiner (d n : ℕ) (E : (Fin d → ℝ) →ₗ[ℝ] Op n)
    (G : Matrix (Fin d) (Fin d) ℝ) (H : Op n)
    (hE : ∀ x, (E x).IsHermitian ∧ Matrix.trace (E x) = 0)
    (hH : star H = -H) (htr : Matrix.trace H = 0)
    (hintertwine : ∀ x, E (G.mulVec x) = H * E x - E x * H) :
    ∀ (t : ℝ) (x : Fin d → ℝ),
      E ((NormedSpace.exp (t • G)).mulVec x) =
        NormedSpace.exp ((t : ℂ) • H) * E x * NormedSpace.exp ((-t : ℂ) • H) ∧
      evolve (E ((NormedSpace.exp (t • G)).mulVec x)) 1 =
        NormedSpace.exp ((t : ℂ) • H) * evolve (E x) 1 * NormedSpace.exp ((-t : ℂ) • H) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P01

end
