-- Prove2me | Theorems.Thm_ScutaruFid_displaced_state_kernel
-- name    : ScutaruFid.displaced_state_kernel
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:58:05.75683+00:00
-- url     : https://prove2.me/theorems/29d00c81-7271-43fe-a4ab-256f57de4375
-- title:
--   Eqs. (15)–(16): displaced squeezed thermal states $W(\alpha,\tau)\rho_2'W(-\alpha,-\tau)$ and their kernels (corrected: $l=2(a+b)\alpha+i\tau$)
-- statement:
--   Let $A$ be a real symmetric positive definite $2\times2$ matrix with $\det A\ge1$ and $u=(\alpha,\tau)\in\mathbb R^2$. Let $a,b$ be given by (12)–(13) from $A$.
--
--   1. Some bounded operator on $L^2(\mathbb R)$ has the kernel `stateKernel A u`, and every such operator is a density operator (trace class, positive, trace $1$ in every Hilbert basis).
--   2. If $\rho_2'$ has the undisplaced kernel `stateKernel A 0` (this is (15)), then $\rho_2=W(\alpha,\tau)\rho_2'W(-\alpha,-\tau)$ has the kernel `stateKernel A u`, i.e. $\langle x|\rho_2|y\rangle=e^{i\tau(x-y)}\langle x-\alpha|\rho_2'|y-\alpha\rangle$.
--   3. Expanded, this kernel is the Gaussian kernel (16),
--   $$
--   \langle x|\rho_2|y\rangle=\exp\big[-(ax^2+\bar ay^2+2bxy)+lx+\bar ly+g\big],
--   $$
--   with
--   $$
--   l=2(a+b)\alpha+i\tau,\qquad g=g'-(a+\bar a+2b)\alpha^2,\qquad g'=-\tfrac12\ln(\pi a_{qq}).
--   $$
--
--   The displaced squeezed thermal states are thus exactly the operators with kernel `stateKernel A u`, which is the class of states of the main theorem.
--
--   Differences from the source:
--   - correction: l = 2(a+d)α + iτ → l = 2(a+b)α + iτ; reason: expanding −a(x−α)² − 2b(x−α)(y−α) gives the x-coefficient 2(a+b)α; for the vacuum displaced by α = 1, τ = 0 (a = d = ½, b = 0) the printed l = 2 gives trace e³ ≠ 1
--   - correction: <x|ρ2|y> = exp[iτ(x − y)] <x−α|ρ′2|x−α> → <x|ρ2|y> = exp[iτ(x − y)] <x−α|ρ′2|y−α>; reason: the printed second argument x−α makes the kernel independent of y; the next display (16) depends on y
--   - generalization: the displaced squeezed thermal states ρ2 = W ρ′2 W(−α, −τ) (asserted to be states) → in addition, existence of an operator with kernel stateKernel A u and that every such operator is a density operator; reason: an added clause the page does not state; it makes the hypotheses of the other theorems satisfiable
--   - encoding: ρ′2 with kernel (15) and constant g′ → the operator with kernel stateKernel A 0, with a, b from (12)–(13) and g′ = −½ ln(π a_qq); reason: g′ is fixed by the trace normalization of p.1 (2(Re a + b) = 1/a_qq)
-- source:
--   Scutaru, Fidelity for displaced squeezed thermal states and the oscillator semigroup, arXiv:quant-ph/9708013v1, eqs. (15)–(16), p.2

import Mathlib
import Definitions.Def_ScutaruFid_L2R
import Definitions.Def_ScutaruFid_IsKernelOperator
import Definitions.Def_ScutaruFid_gaussKernel
import Definitions.Def_ScutaruFid_IsWeylOperator
import Definitions.Def_ScutaruFid_IsDensityOperator
import Definitions.Def_ScutaruFid_stateKernel

namespace ScutaruFid

/-- **Displaced squeezed thermal states**, eqs. (15)–(16) (corrected: `l = 2(a + b)α + iτ`).
Scutaru, arXiv:quant-ph/9708013v1, eqs. (15)–(16), p.2: "If ρ′2 is an undisplaced squeezed thermal
state with: <x|ρ′2|y> = exp[−(ax² + dy² + 2bxy) + g′] (15) then the displaced squeezed thermal state
ρ2 is obtained as ρ2 = W(α, τ)ρ′2W(−α, −τ) and the corresponding kernel is given by
<x|ρ2|y> = exp[iτ(x − y)] <x−α|ρ′2|x−α> i.e. <x|ρ2|y> = exp[−(ax² + dy² + 2bxy) + lx + ky + g] (16)
where l = 2(a+d)α + iτ, k = l̄ and g = g′ − (a+d+2b)α²."

Let `A` be real symmetric positive definite with `det A ≥ 1` and `u = (α, τ)`.
1. Some bounded operator on `L²(ℝ)` has the kernel `stateKernel A u`, and every such operator is a
   density operator (trace class, positive, trace `1` in every Hilbert basis).
2. If `ρ′` has the undisplaced kernel `stateKernel A 0`, then `W(α, τ) ρ′ W(−α, −τ)` has the
   kernel `stateKernel A u`.
3. `stateKernel A u` is the Gaussian kernel (16) with `a, b` from (12)–(13), `d = ā`,
   `l = 2(a + b)α + iτ`, `k = l̄` and `g = g′ − (a + ā + 2b)α²`, `g′ = −½ ln(π a_qq)`.

**Formalization Note** The page prints `l = 2(a+d)α + iτ`; expanding
`−a(x−α)² − 2b(x−α)(y−α)` gives the coefficient `2(a + b)α` of `x` (the page's `<x−α|ρ′2|x−α>`
is a misprint for `<x−α|ρ′2|y−α>`). With the printed `l`, the vacuum displaced by `α = 1`,
`τ = 0` would have trace `e³`. Clause 1 (existence) is not on the page; it makes the theorems
quantifying over operators with kernel `stateKernel A u` non-vacuous. -/
theorem displaced_state_kernel (A : Matrix (Fin 2) (Fin 2) ℝ) (u : Fin 2 → ℝ) (hA : A.PosDef)
    (hdet : 1 ≤ A.det) :
    ((∃ ρ : L2R →L[ℂ] L2R, IsKernelOperator ρ (stateKernel A u)) ∧
      ∀ ρ : L2R →L[ℂ] L2R, IsKernelOperator ρ (stateKernel A u) →
        ∀ (ι : Type) (B : HilbertBasis ι ℂ L2R), IsDensityOperator B ρ) ∧
    (∀ ρ' W W' : L2R →L[ℂ] L2R, IsKernelOperator ρ' (stateKernel A 0) →
      IsWeylOperator W (u 0) (u 1) → IsWeylOperator W' (-u 0) (-u 1) →
        IsKernelOperator (W * ρ' * W') (stateKernel A u)) ∧
    (let a : ℂ := (((A.det + 1) / (4 * A 0 0) : ℝ) : ℂ) - Complex.I * ((A 0 1 / (2 * A 0 0) : ℝ) : ℂ)
     let b : ℂ := ((-(A.det - 1) / (4 * A 0 0) : ℝ) : ℂ)
     let l : ℂ := 2 * (a + b) * (u 0 : ℂ) + Complex.I * (u 1 : ℂ)
     let g : ℂ := ((-(1 / 2) * Real.log (Real.pi * A 0 0) : ℝ) : ℂ) -
       (a + star a + 2 * b) * (u 0 : ℂ) ^ 2
     ∀ x y : ℝ, stateKernel A u x y = gaussKernel a b (star a) l (star l) g x y) := by sorry

end ScutaruFid
