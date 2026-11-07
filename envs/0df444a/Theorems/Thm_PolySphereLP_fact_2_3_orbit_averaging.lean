-- Prove2me | Theorems.Thm_PolySphereLP_fact_2_3_orbit_averaging
-- name    : PolySphereLP.fact_2_3_orbit_averaging
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:58:56.80699+00:00
-- url     : https://prove2.me/theorems/003acaf7-cfd7-46a8-b112-8999e68a9b78
-- title:
--   Fact 2.3 — orbit averaging on a harmonic degree
-- statement:
--   Let $n\ge3$, $k\ge0$, $h_{n,k}=\dim_{\mathbb C}E_{n,k}$, and let $\mu$ be Haar probability measure on $K=SO(n)$ or $K=O(n)$. Write $U_{n,k}(O)=O^{\otimes k}|_{E_{n,k}}$.
--   1. For every Hermitian operator $A:E_{n,k}\to E_{n,k}$,
--   $$\int_K U_{n,k}(O)\,A\,U_{n,k}(O)^*\,d\mu(O)=\frac{\operatorname{tr}A}{h_{n,k}}\,I_{E_{n,k}}. \tag{27}$$
--   2. If $W\subseteq E_{n,k}$ is a complex subspace of dimension $b$ (not necessarily invariant), $A_W$ its Hermitian orthogonal projection, and $T\in E_{n,k}$, then
--   $$\int_K A_{U_{n,k}(O)W}\,d\mu(O)=\frac b{h_{n,k}}\,I_{E_{n,k}},\qquad \mathbb E_{O\sim\mu}\big[\|A_{U_{n,k}(O)W}T\|_F^2\big]=\frac b{h_{n,k}}\,\|T\|_F^2. \tag{28}$$
--   3. For a fixed $S\in E_{n,k}$,
--   $$\int_K (U_{n,k}(O)S)(U_{n,k}(O)S)^*\,d\mu(O)=\frac{\|S\|_F^2}{h_{n,k}}\,I_{E_{n,k}}. \tag{29}$$
--
--   These Schur-averaging identities give the isotropic-restriction energy estimate (Lemma A.5).
--
--   **Formalization Note** Operator identities on $E_{n,k}$ are stated through their entries $\langle\,\cdot\,S,T\rangle_F$ for all $S,T\in E_{n,k}$. A Hermitian operator is a linear map that preserves $E_{n,k}$ and is symmetric for $\langle\cdot,\cdot\rangle_F$ on it, and $\operatorname{tr}A$ is the trace of its restriction to $E_{n,k}$. $U(O)^*$ is $(O^\top)^{\otimes k}$, and $(US)(US)^*X=\langle X,US\rangle_F\,US$.
--
--   Differences from the source:
--   - encoding: Haar probability measure on K → IsHaarProb K μ: a probability measure on entry arrays, carried by K, invariant under left multiplication by K; reason: uniqueness of Haar measure on the compact group K; no matrix measurable space or compact-group instance exists at this Mathlib revision
--   - encoding: operator identities on E_{n,k} (integrals of operators, I_{E_{n,k}}) → identities of the entries ⟨X S, T⟩_F for all S, T ∈ E_{n,k}; reason: the entries determine an operator on E_{n,k}, and integrals of operators are taken entrywise
--   - encoding: Hermitian operator A : E_{n,k} → E_{n,k}, tr A → a linear map on all tensors preserving E_{n,k} and symmetric on it; the trace of its restriction; reason: every Hermitian operator on E_{n,k} extends (e.g. by 0 on the complement) and only the restriction is used
--   - encoding: U(O)* → (Oᵀ)^{⊗k}; reason: the Frobenius adjoint of O^{⊗k} for real O, which preserves E_{n,k}
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), Fact 2.3, p.13, eqs. (27)–(29)

import Mathlib
import Definitions.Def_PolySphereLP_Esp
import Definitions.Def_PolySphereLP_tensorAct
import Definitions.Def_PolySphereLP_orthProjT
import Definitions.Def_PolySphereLP_IsHaarProb
open MvPolynomial MeasureTheory

namespace PolySphereLP

/-- **Fact 2.3 (Orbit averaging on a harmonic degree).** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), Fact 2.3, p.13, eqs. (27)–(29).

Let `n ≥ 3`, `k ≥ 0`, `h_{n,k} = dim_ℂ E_{n,k}`, and `μ` Haar probability measure on `K = SO(n)` or
`K = O(n)`, `U_{n,k}(O) = O^{⊗k}|_{E_{n,k}}`.
1. (27) For every Hermitian operator `A` on `E_{n,k}`: `∫_K U(O) A U(O)* dμ = (tr A / h_{n,k}) I`.
2. (28) For every complex subspace `W ⊆ E_{n,k}` of dimension `b` (not necessarily invariant), with
   `A_W` its Hermitian orthogonal projection: `∫_K A_{U(O)W} dμ = (b/h_{n,k}) I` and, for `T ∈ E_{n,k}`,
   `E_{O∼μ} ‖A_{U(O)W} T‖²_F = (b/h_{n,k}) ‖T‖²_F`.
3. (29) For `S ∈ E_{n,k}`: `∫_K (U(O)S)(U(O)S)* dμ = (‖S‖²_F/h_{n,k}) I`.

**Formalization Note.** Operator identities on `E_{n,k}` are stated through their matrix entries
`⟨· S, T⟩_F` for all `S, T ∈ E_{n,k}`, which determine an operator on `E_{n,k}`. `U(O)*` is
`(Oᵀ)^{⊗k}` (the Frobenius adjoint of `O^{⊗k}` for real `O`); `(US)(US)*X = ⟨X, US⟩_F US`. A Hermitian
operator is a linear map preserving `E_{n,k}` and symmetric for `⟨·,·⟩_F` there; `tr A` is the trace
of its restriction to `E_{n,k}`. Haar measure is `IsHaarProb` (a left-invariant probability measure
carried by `K`, on entry arrays). The integrands are polynomial in the entries of `O`, bounded on `K`,
which carries `μ`, so they are integrable. -/
theorem fact_2_3_orbit_averaging (n : ℕ) (hn : 3 ≤ n) (k : ℕ) (K : Set (Matrix (Fin n) (Fin n) ℝ))
    (hK : K = (Matrix.orthogonalGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ)) ∨
      K = (Matrix.specialOrthogonalGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ)))
    (μ : Measure (Fin n → Fin n → ℝ)) (hμ : IsHaarProb K μ) :
    (∀ (A : Tensor n k →ₗ[ℂ] Tensor n k) (hAE : ∀ T ∈ Esp n k, A T ∈ Esp n k),
      (∀ S ∈ Esp n k, ∀ T ∈ Esp n k, frob (A S) T = frob S (A T)) →
      ∀ S ∈ Esp n k, ∀ T ∈ Esp n k,
        ∫ O, frob (tensorAct k (Matrix.of O) (A (tensorAct k (Matrix.of O).transpose S))) T ∂μ =
          LinearMap.trace ℂ (Esp n k) (A.restrict hAE) / (Module.finrank ℂ (Esp n k) : ℂ) *
            frob S T) ∧
    (∀ W : Submodule ℂ (Tensor n k), W ≤ Esp n k →
      (∀ S ∈ Esp n k, ∀ T ∈ Esp n k,
        ∫ O, frob (orthProjT (W.map (tensorAct k (Matrix.of O))) S) T ∂μ =
          (Module.finrank ℂ W : ℂ) / (Module.finrank ℂ (Esp n k) : ℂ) * frob S T) ∧
      (∀ T ∈ Esp n k,
        ∫ O, frobNormSq (orthProjT (W.map (tensorAct k (Matrix.of O))) T) ∂μ =
          (Module.finrank ℂ W : ℝ) / (Module.finrank ℂ (Esp n k) : ℝ) * frobNormSq T)) ∧
    (∀ S ∈ Esp n k, ∀ X ∈ Esp n k, ∀ Y ∈ Esp n k,
      ∫ O, frob X (tensorAct k (Matrix.of O) S) * frob (tensorAct k (Matrix.of O) S) Y ∂μ =
        ((frobNormSq S / (Module.finrank ℂ (Esp n k) : ℝ) : ℝ) : ℂ) * frob X Y) := by sorry

end PolySphereLP
