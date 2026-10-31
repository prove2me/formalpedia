-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P95_eigenoperatorClassification
-- name    : QAlgorithms.Papers.Independent.Intake100.P95.eigenoperatorClassification
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T15:46:36.277173+00:00
-- url     : https://prove2.me/theorems/dcea202d-cff7-4949-b600-4f2cacef90e7
-- title:
--   Type-I inversion and the constructive tensor eigenbasis
-- statement:
--   Let $n\ge1$ and let $H$ be a Hermitian traceless operator on $n$ qubits. A local operation $K$ is a tensor product of $n$ independent matrices in $\mathrm{SU}(2)$. For each fixed $K$,
--
--   $$K e^{-itH}K^\dagger=e^{itH}\quad(\forall t\in\mathbb R)\quad\Longleftrightarrow\quad KHK^\dagger=-H\quad\Longleftrightarrow\quad(\overline K\otimes K)\operatorname{vec}H=-\operatorname{vec}H.$$
--
--   Consequently type-I membership means that such a single $K$ exists. For every choice of local factors $K_\ell$, choose an orthonormal eigenbasis $v_{\ell,a}$, $a\in\{0,1\}$, with eigenvalues $\lambda_{\ell,a}$. The $-1$ eigenspace of conjugation by $K$ has a linearly independent spanning family
--
--   $$\left\{\bigotimes_{\ell=1}^n |v_{\ell,a_\ell}\rangle\langle v_{\ell,b_\ell}|:\ \prod_{\ell=1}^n\lambda_{\ell,a_\ell}\overline{\lambda_{\ell,b_\ell}}=-1\right\}.$$
--
--   This is the tensor construction with exact branch selection, for all complex operators in that eigenspace. Hamiltonians are obtained by retaining Hermiticity and trace zero. The equation includes $H=0$; no claim makes the union over different $K$ a vector space.
-- source:
--   Which Quantum Evolutions Can Be Reversed by Local Unitary Operations? Algebraic Classification and Gradient-Flow-Based Numerical Checks, arXiv:quant-ph/0610061v1, PDF p. 4, Lemma 4 (1)–(2): eigenoperator criterion and constructive tensor eigenbasis; abstract capstone

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P95

namespace QAlgorithms.Papers.Independent.Intake100.P95

open scoped BigOperators

open QAlgorithms.Papers.Independent.Information100.P32 (Op evolution)

open QAlgorithms.Papers.Independent.Advance50.P38 (comm realHSPairing)

open QAlgorithms.Papers.Independent.Information100.P10 (pauli)

open QAlgorithms.Papers.Independent.Claimed50.P03 (wordMatrix wordSupport)

noncomputable section

/-- Lemma 4(1)–(2), PDF pp.4–5, (15)–(23), and abstract p.1.
A fixed K works for all t. Its -1 eigenspace is given by exactly the selected
products of local spectral vectors, which are linearly independent.
The equation permits H=0; the union over K is not asserted to be a subspace. -/
theorem eigenoperatorClassification {n : ℕ} (hn : 0 < n) (H : Op (QAlgorithms.Qubits n))
    (hH : IsHamiltonian H) :
    (∀ K : LocalSU n,
      ((∀ t : ℝ, localAd K (evolution H t) = evolution H (-t)) ↔
        localAd K H = -H) ∧
      (localAd K H = -H ↔
        (Matrix.kronecker (fun i j => star (localMatrix K i j)) (localMatrix K)).mulVec
          (Matrix.vec H) = -Matrix.vec H)) ∧
    (TypeI H ↔ ∃ K : LocalSU n, localAd K H = -H) ∧
    (∀ K : LocalSU n, ∃ (V : Fin n → Matrix.unitaryGroup Bool ℂ)
      (lam : Fin n → Bool → ℂ),
      (∀ l b, (K l : Matrix Bool Bool ℂ).mulVec
        (fun i => (V l : Matrix Bool Bool ℂ) i b) =
          lam l b • (fun i => (V l : Matrix Bool Bool ℂ) i b)) ∧
      LinearIndependent ℂ (fun q : SelectedPairs lam =>
        productEigenoperator V q.val.1 q.val.2) ∧
      (∀ A : Op (QAlgorithms.Qubits n), localAd K A = -A ↔
        A ∈ Submodule.span ℂ (Set.range (fun q : SelectedPairs lam =>
          productEigenoperator V q.val.1 q.val.2)))) := by sorry

end

end QAlgorithms.Papers.Independent.Intake100.P95
