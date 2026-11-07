-- Prove2me | Theorems.Thm_StochConvexProg_Duality_fenchel_moreau_U
-- name    : StochConvexProg.Duality.fenchel_moreau_U
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-06T14:28:23.434521+00:00
-- url     : https://prove2.me/theorems/e13778a9-81ce-4cb0-87ac-2fe0f4e62840
-- title:
--   Conjugacy theorem on (U, Y): a proper convex weakly lsc φ satisfies φ** = φ
-- statement:
--   Let $\sigma$ be a probability measure on a measurable space $(S,\mathcal S)$ and consider the paired spaces
--   $$U=\mathbb R^{m_1}\times\mathcal L^\infty_{m_2},\qquad Y=\mathbb R^{m_1}\times\mathcal L^1_{m_2},\qquad \langle u,y\rangle=u_1\cdot y_1+\int_S u_2(s)\cdot y_2(s)\,\sigma(ds)$$
--   (the pairing (1.6) of the paper). For $\varphi:U\to[-\infty,+\infty]$ let $\varphi^*(y)=\sup_{u\in U}\{\langle u,y\rangle-\varphi(u)\}$ and $\varphi^{**}(u)=\sup_{y\in Y}\{\langle u,y\rangle-\varphi^*(y)\}$ be its conjugate and biconjugate with respect to this pairing.
--
--   **Theorem (conjugacy theorem for the pairing (1.6)).** Suppose $\varphi$ is
--
--   1. proper: $\varphi(u)>-\infty$ for every $u$ and $\varphi(u)<+\infty$ for some $u$;
--   2. convex: its epigraph $\{(u,\alpha)\in U\times\mathbb R : \varphi(u)\le\alpha\}$ is convex;
--   3. lower semicontinuous with respect to the weak topology $\sigma(U,Y)$ on $U$ induced by the pairing.
--
--   Then
--   $$\varphi^{**}=\varphi .$$
--
--   This is the final step of the proof of Theorem 3 of Rockafellar–Wets: once the perturbation function $\varphi$ is known to be a proper convex function that is lower semicontinuous "in a topology compatible with the pairing between $U$ and $Y$", one has $\varphi^{**}=\varphi$. It is the Fenchel–Moreau theorem specialised to this dual pair.
--
--   **Formalization Note** Values are in `EReal`; the weak topology is `weakU`, the infimum over $y\in Y$ of the topologies induced by $u\mapsto\langle u,y\rangle$, passed explicitly since $U$ also carries its norm topology. Conjugates are `conjU`, `biconjU` from the shared definition file.
-- source:
--   Rockafellar and Wets, Stochastic convex programming: basic duality, Pacific J. Math. 62(1) (1976), p. 191, end of the proof of Theorem 3 ("Inasmuch as φ is a proper convex function on U which is lower semicontinuous in a topology compatible with the pairing between U and Y, we have φ** = φ"), invoking the conjugacy theorem of Rockafellar, Conjugate Duality and Optimization, SIAM 1974 (ref. [8]), Theorem 5. https://msp.org/pjm/1976/62-1/p20.xhtml

import Mathlib
import Definitions.Def_StochConvexProg_Duality_Problem
import Definitions.Def_StochConvexProg_Duality_Dual

open MeasureTheory

namespace StochConvexProg.Duality

/-- Rockafellar–Wets (1976), p. 191, last step of the proof of Theorem 3 (the conjugacy theorem of
Rockafellar, *Conjugate Duality and Optimization*, 1974, Theorem 5, for the pairing (1.6)): a proper
convex function `φ : U → [−∞, +∞]` that is lower semicontinuous for the weak topology induced on
`U = R^{m₁} × ℒ^∞_{m₂}` by `Y = R^{m₁} × ℒ¹_{m₂}` satisfies `φ** = φ`. -/
theorem fenchel_moreau_U {S : Type*} [MeasurableSpace S] {σ : Measure S}
    [IsProbabilityMeasure σ] {m₁ m₂ : ℕ} (φ : USpace σ m₁ m₂ → EReal)
    (hproper : EProper φ) (hconv : EConvex φ)
    (hlsc : @LowerSemicontinuous (USpace σ m₁ m₂) EReal (weakU σ m₁ m₂) _ φ) :
    biconjU φ = φ := by sorry

end StochConvexProg.Duality
