-- Prove2me | Theorems.Thm_TensorProduct_AlgebraTensorModule_cancelBaseChange_baseChange_baseChange_apply
-- name    : TensorProduct.AlgebraTensorModule.cancelBaseChange_baseChange_baseChange_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:02.683932+00:00
-- url     : https://prove2.me/theorems/14772062-a63f-5055-b24d-3f9b3528e980
-- title:
--   Cancellation of iterated base change is natural in endomorphisms
-- statement:
--   Let $q$ be a prime natural number, and write $\mathbb{Z}_{q}$ and $\mathbb{Q}_{q}$ for the $q$-adic integers and the $q$-adic numbers. Let $\Lambda$ be an additive commutative group, regarded as a $\mathbb{Z}$-module, and let $f \colon \Lambda \to \Lambda$ be a $\mathbb{Z}$-linear endomorphism. Consider the canonical cancellation isomorphism $\gamma =$ `cancelBaseChange ℤ ℤ_[q] ℚ_[q] ℚ_[q] Λ`, the $\mathbb{Q}_{q}$-linear equivalence $\mathbb{Q}_{q} \otimes_{\mathbb{Z}_{q}} (\mathbb{Z}_{q} \otimes_{\mathbb{Z}} \Lambda) \cong \mathbb{Q}_{q} \otimes_{\mathbb{Z}} \Lambda$ determined by $a \otimes (b \otimes \lambda) \mapsto b a \otimes \lambda$. The assertion is that for every element $x$ of $\mathbb{Q}_{q} \otimes_{\mathbb{Z}_{q}} (\mathbb{Z}_{q} \otimes_{\mathbb{Z}} \Lambda)$ one has $\gamma\bigl((f_{\mathbb{Z}_{q}})_{\mathbb{Q}_{q}}(x)\bigr) = f_{\mathbb{Q}_{q}}\bigl(\gamma(x)\bigr)$, where $f_{\mathbb{Z}_{q}} = \mathrm{id} \otimes f$ is the base change of $f$ along $\mathbb{Z} \to \mathbb{Z}_{q}$, $(f_{\mathbb{Z}_{q}})_{\mathbb{Q}_{q}}$ its further base change along $\mathbb{Z}_{q} \to \mathbb{Q}_{q}$, and $f_{\mathbb{Q}_{q}}$ the base change of $f$ directly along $\mathbb{Z} \to \mathbb{Q}_{q}$. The statement is the pointwise (elementwise) form of the commuting square, not an equality of linear maps.
--
--   This is the naturality, with respect to endomorphisms of $\Lambda$, of the transitivity-of-scalar-extension isomorphism $\mathbb{Q}_{q} \otimes_{\mathbb{Z}_{q}} (\mathbb{Z}_{q} \otimes_{\mathbb{Z}} \Lambda) \cong \mathbb{Q}_{q} \otimes_{\mathbb{Z}} \Lambda$: extending scalars from $\mathbb{Z}$ to $\mathbb{Q}_{q}$ in two steps or in one gives the same operator. It is used in [`ModularCurve.exists_linearEquiv_rationalTateModule_tensor_periodLattice`](thm.html#ModularCurve.exists_linearEquiv_rationalTateModule_tensor_periodLattice) to transport an operator between the rational Tate module and the $\mathbb{Q}_{q}$-scalar extension of a period lattice.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_TensorProduct_AlgebraTensorModule_cancelBaseChange_baseChange_baseChange_apply.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

theorem TensorProduct.AlgebraTensorModule.cancelBaseChange_baseChange_baseChange_apply
    (q : ℕ) [Fact q.Prime] (Λ : Type) [AddCommGroup Λ] (f : Λ →ₗ[ℤ] Λ)
    (x : ℚ_[q] ⊗[ℤ_[q]] (ℤ_[q] ⊗[ℤ] Λ)) :
    cancelBaseChange ℤ ℤ_[q] ℚ_[q] ℚ_[q] Λ (((f.baseChange ℤ_[q]).baseChange ℚ_[q]) x) =
      (f.baseChange ℚ_[q]) (cancelBaseChange ℤ ℤ_[q] ℚ_[q] ℚ_[q] Λ x) := by sorry
