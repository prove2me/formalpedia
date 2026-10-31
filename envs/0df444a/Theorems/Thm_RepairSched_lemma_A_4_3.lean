-- Prove2me | Theorems.Thm_RepairSched_lemma_A_4_3
-- name    : RepairSched.lemma_A_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:47:46.659632+00:00
-- url     : https://prove2.me/theorems/6b682a16-884e-4617-90ed-ee060a474161
-- title:
--   Lemma A.4.3, OA p.23 — the two-sided regulator with drift $\lambda(w-s)^+$
-- statement:
--   Let $b>0$, $\lambda,s\ge0$, and let $x\in\mathbb D$ with $x(0)\in[0,b]$. There is a unique $(w,\ell,u)\in\mathbb D^3$ with
--   $$w(t)=x(t)-\lambda\int_0^t(w(y)-s)^+\,dy+\ell(t)-u(t)\in[0,b],$$
--   $\ell(0)=u(0)=0$, $\ell,u$ nondecreasing and $\int w\,d\ell=\int(b-w)\,du=0$. The map $x\mapsto(w,\ell,u)$ is non-anticipative: inputs agreeing on $[0,t]$ give triples agreeing on $[0,t]$.
--
--   This is the Lipschitz building block of the regulator analysis.
--
--   Differences from the source:
--   - encoding: triples (φ,ψ₁,ψ₂) as a mapping → existence and uniqueness of triples with C1–C3; non-anticipativity for any two inputs agreeing on [0,t]; reason: a mapping is exactly a unique solution for each input
--   - encoding: C1's integral ∫₀ᵗ (drift)(w(y)) dy and C3: ∫₀^∞ w dℓ = ∫₀^∞ (b − w) du = 0 → the drift path y ↦ β(w(y)) interval-integrable on every [0,t]; dℓ, du as Stieltjes measures of ℓ, u extended by 0 to t < 0, giving no mass to {w > 0} resp. {w < b} on [0,∞); reason: β∘w is bounded and measurable for càdlàg w with values in [0,b], so integrability excludes no triple; since w ∈ [0,b] the two vanishing integrals say exactly that these sets are null
-- source:
--   Özkan and van Houtum, Joint Inventory and Scheduling Control in a Repair Facility, SSRN 3784144 (2023), Definition A.4.2 and Lemma A.4.3, OA p.23

import Mathlib
import Definitions.Def_RepairSched_IsRegulated

open Set

namespace RepairSched

/-- **Lemma A.4.3: the two-sided regulator with drift `λ(w − s)⁺`.**
Özkan and van Houtum, *Joint Inventory and Scheduling Control in a Repair Facility*, SSRN 3784144 (2023), Definition A.4.2 and Lemma A.4.3, OA p.23 (PDF p.63).

For `b > 0`, `λ, s ≥ 0` and `x ∈ D` with `x(0) ∈ [0,b]`, there is a triple `(w, ℓ, u) ∈ D³` with
C1–C3 of Definition A.4.2, it is unique, and it is non-anticipative with respect to `x`: if two
inputs agree on `[0,t]`, then their triples agree on `[0,t]`.

**Formalization Note.** The last clause gives uniqueness at once by taking `x₁ = x₂`; uniqueness
is stated separately to match the printed lemma. -/
theorem lemma_A_4_3 (b lam s : ℝ) (hb : 0 < b) (hlam : 0 ≤ lam) (hs : 0 ≤ s) :
    (∀ x, IsCadlag x → x 0 ∈ Icc 0 b →
      (∃ w l u, IsRegulated (fun v => lam * max (v - s) 0) b x w l u) ∧
      ∀ w₁ l₁ u₁ w₂ l₂ u₂, IsRegulated (fun v => lam * max (v - s) 0) b x w₁ l₁ u₁ →
        IsRegulated (fun v => lam * max (v - s) 0) b x w₂ l₂ u₂ →
        EqOn w₁ w₂ (Ici 0) ∧ EqOn l₁ l₂ (Ici 0) ∧ EqOn u₁ u₂ (Ici 0)) ∧
    ∀ x₁ x₂ t, IsCadlag x₁ → IsCadlag x₂ → x₁ 0 ∈ Icc 0 b → x₂ 0 ∈ Icc 0 b → 0 ≤ t →
      EqOn x₁ x₂ (Icc 0 t) →
      ∀ w₁ l₁ u₁ w₂ l₂ u₂, IsRegulated (fun v => lam * max (v - s) 0) b x₁ w₁ l₁ u₁ →
        IsRegulated (fun v => lam * max (v - s) 0) b x₂ w₂ l₂ u₂ →
        EqOn w₁ w₂ (Icc 0 t) ∧ EqOn l₁ l₂ (Icc 0 t) ∧ EqOn u₁ u₂ (Icc 0 t) := by sorry

end RepairSched
