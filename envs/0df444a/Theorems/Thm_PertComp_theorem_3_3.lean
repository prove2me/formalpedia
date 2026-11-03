-- Prove2me | Theorems.Thm_PertComp_theorem_3_3
-- name    : PertComp.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:15:29.771671+00:00
-- url     : https://prove2.me/theorems/30d7fe9f-5902-4415-855a-0e8bb05767a0
-- title:
--   Theorem 3.3: Lagrangian, dual problem and Kuhn–Tucker operator of the perturbation (1.8)
-- statement:
--   Consider the setting of Problem 1.1: $X,Y$ reflexive real Banach spaces, $\varphi\in\Gamma_0(\mathbb R)$ increasing and not constant, $f,h\in\Gamma_0(X)$, $g,\ell\in\Gamma_0(Y)$, $L\colon X\to Y$ linear and bounded, and the qualification conditions [a]–[d]. Let $F$ be the perturbation function (1.8), and set
--   $$D=\operatorname{dom} f\cap\operatorname{dom} h,\qquad V=\operatorname{dom}\varphi^*\times(\operatorname{dom} g^*\cap\operatorname{dom}\ell^*).$$
--   Then the following hold.
--
--   1. The Lagrangian $\mathscr L_F\colon X\times\mathbb R\times Y^*\to[-\infty,+\infty]$ is
--   $$\mathscr L_F(x,\xi^*,y^*)=\begin{cases}+\infty, & x\notin D;\\ (\xi^*\odot f)(x)+h(x)+\langle Lx,y^*\rangle-\varphi^*(\xi^*)-g^*(y^*)-\ell^*(y^*), & x\in D,\ (\xi^*,y^*)\in V;\\ -\infty, & x\in D,\ (\xi^*,y^*)\notin V.\end{cases}$$
--   2. The dual problem is
--   $$\underset{(\xi^*,y^*)\in\mathbb R\times Y^*}{\text{minimize}}\ \varphi^*(\xi^*)+\big(h^*\,\Box\,\widetilde{f^*}(\cdot,\xi^*)\big)(-L^*y^*)+g^*(y^*)+\ell^*(y^*).$$
--   3. The Kuhn–Tucker operator $\mathscr K_F\colon X\times\mathbb R\times Y^*\to 2^{X^*\times\mathbb R\times Y}$ is
--   $$\mathscr K_F(x,\xi^*,y^*)=\begin{cases}\big(\partial(\xi^*\odot f)(x)+\partial h(x)+L^*y^*\big)\times\big(\partial\varphi^*(\xi^*)-f(x)\big)\times\big(\partial g^*(y^*)+\partial\ell^*(y^*)-Lx\big), & x\in D,\ (\xi^*,y^*)\in V;\\ \varnothing, & x\notin D\ \text{or}\ (\xi^*,y^*)\notin V.\end{cases}$$
--   4. With $\mathscr D$ the set of solutions of the dual problem in 2, $\operatorname{zer}\mathscr K_F\subset\mathscr P\times\mathscr D$.
--   5. $\mathscr P=\bigcup_{(\xi^*,y^*)\in\mathbb R\times Y^*}\{x\in X : (x,\xi^*,y^*)\in\operatorname{zer}\mathscr K_F\}$.
--
--   The theorem turns Problem 1.1, a minimization with a nonlinear composite term $\varphi\circ f$, into the search for a zero of a single set-valued operator on $X\times\mathbb R\times Y^*$ whose zeros are primal–dual solution pairs; the paper's algorithms split this operator.
--
--   **Formalization Note** Item 2 is stated as the identity of the dual objective $\sup_x(-\mathscr L_F(x,\xi^*,y^*))$ of (2.25) with the function displayed in (3.11), at every $(\xi^*,y^*)\in\mathbb R\times Y^*$. All five items are one conjunction.
--
--   Differences from the source:
--   - encoding: functions with values in ]−∞, +∞] or [−∞, +∞] → EReal-valued functions; a function of Γ₀ never takes ⊥; reason: Lean convention; same instances
--   - encoding: reflexive real Banach space → NormedSpace ℝ with [CompleteSpace] and IsReflexive (the canonical map into the bidual is onto); reason: Mathlib has no reflexivity class; same spaces
--   - reading: φ increasing → Monotone φ (nondecreasing); reason: the paper's usage: Example 1.2 takes φ = ι_{]−∞,0]}, which is not strictly increasing
--   - encoding: X ⊕ U with the Euclidean product norm (2.2) → Lean product X × U (sup norm); reason: equivalent norms: same topology, same pairing (2.1)
--   - encoding: φ*, ∂φ and ∂φ* with ℝ* identified with ℝ; the real dual variable ξ* → PWDB.conj φ (the conjugate on the inner-product space ℝ, ⟨t, s⟩ = t s), subdiffR, and realDual ξ* = (ξ ↦ ξ ξ*) as the element of StrongDual ℝ ℝ; reason: canonical isomorphism ℝ ≅ ℝ*; same values
--   - encoding: dual variable (ξ*, y*) ∈ ℝ × Y* of the perturbation space U = ℝ ⊕ Y → dualPair ξ* y* = ((ξ, y) ↦ ξ ξ* + ⟨y, y*⟩) ∈ StrongDual ℝ (ℝ × Y); reason: the pairing (2.1) identifies (ℝ ⊕ Y)* with ℝ × Y*; same objects
--   - encoding: subgradients of a function on a dual space V* lie in V** = V → subdiffPre: the points of V whose canonical image in V** is a subgradient; reason: reflexivity identifies V** with V; same sets
--   - reading: (2.6) defines ∂f for proper f, while (2.26) applies ∂ to Lagrangians that can be improper → the formula (2.6) applied to every EReal-valued function (RockafellarMaxMono.Shared.subdiff); reason: this is how the paper's proofs of (3.3) and (3.12) evaluate ∂ off V and off the domain
--   - reading: "the dual problem is (3.11)" → the objective sup_x(−𝓛_F(x, ξ*, y*)) of (2.25) equals the objective of (3.11) at every (ξ*, y*) ∈ ℝ × Y*; reason: (2.25) and (3.11) are minimization problems over the same set, so they are the same problem when their objectives agree
-- source:
--   L. M. Briceño-Arias, P. L. Combettes, A Perturbation Framework for Convex Minimization and Monotone Inclusion Problems with Nonlinear Compositions, arXiv:2111.11421v4, Theorem 3.3, p.12 (proof pp.12–13)

import Mathlib
import Definitions.Def_RockafellarMaxMono_Shared_Conj
import Definitions.Def_RockafellarMaxMono_Shared_Subdiff
import Definitions.Def_PertComp_Problem11
import Definitions.Def_PertComp_primalSet
import Definitions.Def_PertComp_pert
import Definitions.Def_PertComp_lag
import Definitions.Def_PertComp_dualObj
import Definitions.Def_PWDB_conj
import Definitions.Def_PertComp_subdiffR
import Definitions.Def_PertComp_subdiffPre
import Definitions.Def_PertComp_odot
import Definitions.Def_RockafellianRelax_argmin

namespace PertComp

open Pointwise

open Classical in
/-- Briceño-Arias, Combettes, arXiv:2111.11421v4, **Theorem 3.3**, p.12: consider the setting of
Problem 1.1, set `D = dom f ∩ dom h` and `V = dom φ* × (dom g* ∩ dom ℓ*)`, and let `F` be the
perturbation (1.8). Then:
(i) the Lagrangian is `𝓛_F(x, ξ*, y*) = +∞` if `x ∉ D`;
  `(ξ* ⊙ f)(x) + h(x) + ⟨Lx, y*⟩ − φ*(ξ*) − g*(y*) − ℓ*(y*)` if `x ∈ D` and `(ξ*, y*) ∈ V`;
  `−∞` if `x ∈ D` and `(ξ*, y*) ∉ V` (3.10);
(ii) the dual problem (2.25) is (3.11): its objective `sup_x (−𝓛_F(x, ξ*, y*))` equals
  `φ*(ξ*) + (h* □ \widetilde{f*}(·, ξ*))(−L*y*) + g*(y*) + ℓ*(y*)` for every `(ξ*, y*) ∈ ℝ × Y*`;
(iii) the Kuhn–Tucker operator is
  `𝒦_F(x, ξ*, y*) = (∂(ξ* ⊙ f)(x) + ∂h(x) + L*y*) × (∂φ*(ξ*) − f(x)) × (∂g*(y*) + ∂ℓ*(y*) − Lx)`
  if `x ∈ D` and `(ξ*, y*) ∈ V`, and `∅` if `x ∉ D` or `(ξ*, y*) ∉ V` (3.12);
(iv) with `𝒟` the set of solutions of (3.11), `zer 𝒦_F ⊂ 𝒫 × 𝒟`;
(v) `𝒫 = ⋃_{(ξ*, y*) ∈ ℝ × Y*} {x ∈ X | (x, ξ*, y*) ∈ zer 𝒦_F}`.

**Formalization Note.** `𝓛_F`, the dual objective and `𝒦_F` are the generic objects of
Definition 2.10 (`lag`, `dualFun`, `kt`, `zerKt`) for `Φ = F` (`pert`) and `U = ℝ ⊕ Y`; the
paper's dual variable `(ξ*, y*) ∈ ℝ × Y*` is the functional `dualPair ξ* y* = ((ξ, y) ↦
ξ ξ* + ⟨y, y*⟩)` of `(ℝ ⊕ Y)*`. Subgradients of functions on `Y*` (`∂g*`, `∂ℓ*`) are taken in
`Y` (`subdiffPre`); `φ*` is `PWDB.conj φ` (the published conjugate, on `ℝ`) and `∂φ*` is
`subdiffR`; `L*y*` is `y'.comp L`. Sums and
differences of sets are pointwise. `𝒫` is `primalSet` and `𝒟` is `Argmin` of `dualObj`
(`RockafellianRelax.argmin`: minimizers inside the domain, as on p.5). -/
theorem theorem_3_3 {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (φ : ℝ → EReal) (f : X → EReal) (g ℓ : Y → EReal) (L : X →L[ℝ] Y) (h : X → EReal)
    (hP : Problem11 φ f g ℓ L h) :
    -- (i) the Lagrangian (3.10)
    (∀ (x : X) (ξ' : ℝ) (y' : StrongDual ℝ Y),
      lag (pert φ f g ℓ L h) x (dualPair ξ' y') =
        if ¬ (f x ≠ ⊤ ∧ h x ≠ ⊤) then ⊤
        else if PWDB.conj φ ξ' ≠ ⊤ ∧ RockafellarMaxMono.Shared.conj g y' ≠ ⊤ ∧
            RockafellarMaxMono.Shared.conj ℓ y' ≠ ⊤ then
          odot ξ' f x + h x + ((y' (L x) : ℝ) : EReal) - PWDB.conj φ ξ' -
            RockafellarMaxMono.Shared.conj g y' - RockafellarMaxMono.Shared.conj ℓ y'
        else ⊥) ∧
    -- (ii) the dual problem (3.11)
    (∀ (ξ' : ℝ) (y' : StrongDual ℝ Y),
      dualFun (pert φ f g ℓ L h) (dualPair ξ' y') = dualObj φ f g ℓ L h ξ' y') ∧
    -- (iii) the Kuhn–Tucker operator (3.12)
    (∀ (x : X) (ξ' : ℝ) (y' : StrongDual ℝ Y),
      kt (pert φ f g ℓ L h) x (dualPair ξ' y') =
        if (f x ≠ ⊤ ∧ h x ≠ ⊤) ∧ (PWDB.conj φ ξ' ≠ ⊤ ∧ RockafellarMaxMono.Shared.conj g y' ≠ ⊤ ∧
            RockafellarMaxMono.Shared.conj ℓ y' ≠ ⊤) then
          (RockafellarMaxMono.Shared.subdiff (odot ξ' f) x +
              RockafellarMaxMono.Shared.subdiff h x + {y'.comp L}) ×ˢ
            ((subdiffR (PWDB.conj φ) ξ' - {(f x).toReal}) ×ˢ
              (subdiffPre (RockafellarMaxMono.Shared.conj g) y' +
                subdiffPre (RockafellarMaxMono.Shared.conj ℓ) y' - {L x}))
        else ∅) ∧
    -- (iv) zer 𝒦_F ⊂ 𝒫 × 𝒟
    (∀ (x : X) (ξ' : ℝ) (y' : StrongDual ℝ Y),
      (x, dualPair ξ' y') ∈ zerKt (pert φ f g ℓ L h) →
        x ∈ primalSet φ f g ℓ L h ∧
          (ξ', y') ∈
            RockafellianRelax.argmin (fun p : ℝ × StrongDual ℝ Y => dualObj φ f g ℓ L h p.1 p.2)) ∧
    -- (v) 𝒫 is the projection of zer 𝒦_F
    primalSet φ f g ℓ L h =
      ⋃ p : ℝ × StrongDual ℝ Y, {x : X | (x, dualPair p.1 p.2) ∈ zerKt (pert φ f g ℓ L h)} := by sorry

end PertComp
