-- Prove2me | Theorems.Thm_TeschlQM_SturmLiouville_lagrange_identity
-- name    : TeschlQM.SturmLiouville.lagrange_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-28T10:47:08.121661+00:00
-- url     : https://prove2.me/theorems/e1320840-5c9f-4a1a-ba28-c54db5cd649d
-- title:
--   Eq. (9.7) — Lagrange identity on $\mathfrak{D}(\tau)$
-- statement:
--   Let $(a,b,p,q,r)$ be Sturm–Liouville data and $f, g \in \mathfrak{D}(\tau)$. Then the boundary Wronskians $W_a(g^*, f) = \lim_{x\to a} W_x(g^*, f)$ and $W_b(g^*, f) = \lim_{x \to b} W_x(g^*, f)$ exist, and
--   $$\langle g, \tau f\rangle = W_a(g^*, f) - W_b(g^*, f) + \langle \tau g, f\rangle,$$
--   where $\langle u, v\rangle = \int_a^b u(x)^* v(x) r(x)\,dx$ is the inner product of $L^2(I, r\,dx)$.
--
--   The identity shows that $\tau$ on $\mathfrak{D}(\tau)$ fails to be symmetric exactly by boundary terms, which is why self-adjoint realizations are described by conditions on $W_a$ and $W_b$.
--
--   **Formalization Note.** $\tau f$ and $\tau g$ are given as functions $F, G \in L^2(I, r\,dx)$ with $\tau f = F$, $\tau g = G$. Existence of the limits is stated as convergence of $W_x$ to $W_a$ (resp. $W_b$) as defined via `limUnder`. The two integrands are asserted to be integrable, so both sides are genuine inner products. The book prints the boundary term as $W_b(g^*, f) - W_a(g^*, f)$, which has the wrong sign for the Wronskian (9.5): on $(0,1)$ with $p = r = 1$, $q = 0$, $f = x^2$, $g = 1$ the left side is $-2$ and $W_1 - W_0 = 2$. The corrected sign is stated.
-- source:
--   Teschl, Mathematical Methods in Quantum Mechanics, AMS GSM 99, 2009, p. 182, Section 9.1, Eq. (9.7)

import Mathlib
import Definitions.Def_TeschlQM_SturmLiouville_maxDomain
import Definitions.Def_TeschlQM_SturmLiouville_wronskian

namespace TeschlQM.SturmLiouville

open MeasureTheory Filter Topology

/-- Teschl, Eq. (9.7), p. 182. For `f, g ∈ D(τ)` (with `τ f = F`, `τ g = G`) the limits
`W_a(g*, f) = lim_{x→a} W_x(g*, f)` and `W_b(g*, f) = lim_{x→b} W_x(g*, f)` exist, and
`⟨g, τ f⟩ = W_a(g*, f) − W_b(g*, f) + ⟨τ g, f⟩`, where `⟨u, v⟩ = ∫_a^b u(x)* v(x) r(x) dx` (9.2).
The two integrands are integrable (as products of `L²(I, r dx)` functions), so both sides are the
book's inner products.
**Sign correction.** The page prints `W_b(g*, f) − W_a(g*, f)` (and `W_d − W_c` in (9.4)). With the
Wronskian (9.5), `W_x(f₁, f₂) = f₁ (p f₂′) − (p f₁′) f₂`, integration by parts gives the opposite
sign: on `(0, 1)` with `p = r = 1`, `q = 0`, `f = x²`, `g = 1` one has `⟨g, τ f⟩ = −2`,
`W_1(g*, f) − W_0(g*, f) = 2`, `⟨τ g, f⟩ = 0`. The corrected identity is stated. -/
theorem lagrange_identity (L : SLData) (f g F G : ℝ → ℂ)
    (hf : MemLp f 2 L.measure) (hg : MemLp g 2 L.measure)
    (hF : SolvesTau L f F) (hG : SolvesTau L g G)
    (hF2 : MemLp F 2 L.measure) (hG2 : MemLp G 2 L.measure) :
    Tendsto (fun x => wronskian L x (fun y => starRingEnd ℂ (g y)) f) L.atLeft
        (𝓝 (wronskianLeft L (fun y => starRingEnd ℂ (g y)) f)) ∧
      Tendsto (fun x => wronskian L x (fun y => starRingEnd ℂ (g y)) f) L.atRight
        (𝓝 (wronskianRight L (fun y => starRingEnd ℂ (g y)) f)) ∧
      Integrable (fun x => starRingEnd ℂ (g x) * F x) L.measure ∧
      Integrable (fun x => starRingEnd ℂ (G x) * f x) L.measure ∧
      ∫ x, starRingEnd ℂ (g x) * F x ∂L.measure =
        wronskianLeft L (fun y => starRingEnd ℂ (g y)) f -
          wronskianRight L (fun y => starRingEnd ℂ (g y)) f +
          ∫ x, starRingEnd ℂ (G x) * f x ∂L.measure := by sorry

end TeschlQM.SturmLiouville
