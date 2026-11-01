-- Prove2me | Theorems.Thm_ScutaruFid_characteristic_function
-- name    : ScutaruFid.characteristic_function
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:58:23.496447+00:00
-- url     : https://prove2.me/theorems/76c1b87c-f321-4290-8020-b0e2856ad023
-- title:
--   Eqs. (10)–(11): characteristic function $\operatorname{trace}(W(\alpha,\tau)\rho)$ of a Gaussian state (corrected: $\alpha$ paired with $a_{pp}$, cross-term sign, displacement phase)
-- statement:
--   Let $A=\begin{pmatrix}a_{qq}&a_{pq}\\ a_{pq}&a_{pp}\end{pmatrix}$ be a real symmetric positive definite matrix with $\det A\ge1$, let $u=(\alpha_0,\tau_0)\in\mathbb R^2$, and let $\rho$ be the operator with kernel `stateKernel A u`. For every Weyl operator $W(\alpha,\tau)$, $(W(\alpha,\tau)\psi)(x)=e^{i\tau(x-\alpha/2)}\psi(x-\alpha)$, and every Hilbert basis used for the trace,
--
--   $$
--   \operatorname{trace}\big(W(\alpha,\tau)\rho\big)=e^{\,i(\tau\alpha_0-\alpha\tau_0)}\exp\Big[-\tfrac14\big(a_{pp}\alpha^2+a_{qq}\tau^2-2a_{pq}\alpha\tau\big)\Big].
--   $$
--
--   Since $W(\alpha,\tau)=e^{i(\tau Q-\alpha P)}$, this says that $\rho$ is the Gaussian state with means $\langle Q\rangle=\alpha_0$, $\langle P\rangle=\tau_0$ and with $a_{qq}=2(\langle Q^2\rangle-\langle Q\rangle^2)$, $a_{pp}=2(\langle P^2\rangle-\langle P\rangle^2)$, $a_{pq}=2(\tfrac12\langle QP+PQ\rangle-\langle Q\rangle\langle P\rangle)$ as in (11). It is the result that identifies the matrix $A$ and the vector $u$ in the main formula (17).
--
--   Differences from the source:
--   - correction: trace(W(α, τ)ρ) = exp[−¼(a_qq α² + a_pp τ² + 2a_pq ατ)] → trace(W(α, τ)ρ) = exp(i(τα₀ − ατ₀)) · exp[−¼(a_pp α² + a_qq τ² − 2a_pq ατ)]; reason: with the printed W(α, τ) = exp(i(τQ − αP)) the variance of τQ − αP gives this form; for the squeezed vacuum A = diag(2, ½), u = 0, trace(W(1, 0)ρ) = ⟨ψ, ψ(· − 1)⟩ = e^{−1/8}, while the printed value is e^{−1/2}; the phase is the mean of τQ − αP
--   - encoding: the density operator ρ with the moments a_qq, a_pp, a_pq of (11) → the operator with kernel stateKernel A u, A symmetric positive definite with det A ≥ 1; reason: every Gaussian density operator has this form (density_kernel_conditions, kernel_coeffs_of_cov); Q and P are unbounded, so the moments are read off the characteristic function, which determines them
--   - encoding: trace → operatorTrace in an arbitrary Hilbert basis; reason: W(α, τ)ρ is trace class, so the trace is basis-independent
-- source:
--   Scutaru, Fidelity for displaced squeezed thermal states and the oscillator semigroup, arXiv:quant-ph/9708013v1, eqs. (10)–(11), p.2

import Mathlib
import Definitions.Def_ScutaruFid_L2R
import Definitions.Def_ScutaruFid_IsKernelOperator
import Definitions.Def_ScutaruFid_IsWeylOperator
import Definitions.Def_ScutaruFid_stateKernel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P13

open QAlgorithms.Papers.Independent.Dependency50.P13

namespace ScutaruFid

/-- **Characteristic function of a Gaussian state**, eqs. (10)–(11) (corrected: `α` paired with
`a_pp`, sign of the cross term, displacement phase). Scutaru, arXiv:quant-ph/9708013v1, eqs.
(10)–(11), p.2: "The characteristic function of the density operator ρ is given by [11, 16]
CFρ(α, τ) = trace(W(α, τ)ρ) = exp[−¼(a_qq α² + a_pp τ² + 2a_pq ατ)] (10) where
(W(α, τ)ψ)(x) = exp[iτ(x − α/2)]ψ(x − α), a_qq = 2(<Q²> − <Q>²), a_pp = 2(<P²> − <P>²),
a_pq = 2(½<QP + PQ> − <Q><P>)".

Let `A` be a real symmetric positive definite `2 × 2` matrix with `det A ≥ 1`, `u = (α₀, τ₀)`, and
`ρ` the operator with kernel `stateKernel A u`. For every Weyl operator `W(α, τ)` and every Hilbert
basis of `L²(ℝ)`,
`trace(W(α, τ)ρ) = exp(i(τα₀ − ατ₀)) · exp[−¼(a_pp α² + a_qq τ² − 2a_pq ατ)]`,
where `a_qq = A₀₀`, `a_pq = A₀₁`, `a_pp = A₁₁`.

**Formalization Note** This pins `A` as the matrix of (11) (twice the covariance matrix of
`(Q, P)`) and `u` as the vector of means `(<Q>, <P>)` of the state `stateKernel A u`. With the
printed `W(α, τ) = exp(i(τQ − αP))`, the printed (10) has `α` and `τ` interchanged in the
quadratic form, the wrong sign on the cross term (for `a_pq ≠ 0`) and no phase; e.g. for the
squeezed vacuum `A = diag(2, ½)`, `u = 0`, `trace(W(1, 0)ρ) = e^{−1/8}`, not the printed `e^{−1/2}`. -/
theorem characteristic_function (A : Matrix (Fin 2) (Fin 2) ℝ) (u : Fin 2 → ℝ) (hA : A.PosDef)
    (hdet : 1 ≤ A.det) (ρ : L2R →L[ℂ] L2R) (hK : IsKernelOperator ρ (stateKernel A u))
    (W : L2R →L[ℂ] L2R) (α τ : ℝ) (hW : IsWeylOperator W α τ)
    {ι : Type*} (B : HilbertBasis ι ℂ L2R) :
    operatorTrace B (W * ρ) =
      Complex.exp (Complex.I * ((τ * u 0 - α * u 1 : ℝ) : ℂ)) *
        Complex.exp ((-(1 / 4) * (A 1 1 * α ^ 2 + A 0 0 * τ ^ 2 - 2 * A 0 1 * α * τ) : ℝ) : ℂ) := by sorry

end ScutaruFid
