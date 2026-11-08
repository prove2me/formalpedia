-- Prove2me | Theorems.Thm_PoSUndirected_lemma_A_5_incumbent_payments
-- name    : PoSUndirected.lemma_A_5_incumbent_payments
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T08:00:43.480105+00:00
-- url     : https://prove2.me/theorems/e1461f43-afe2-43ca-88dc-e1e62d624d46
-- title:
--   Lemma A.5 — incumbent payments on floors, shifted chords and pendants
-- statement:
--   Consider the host of finite depth $d$ at $\eta(t)$, $0\le t<1$ rational, a weak equilibrium $A$, and a gadget of a block $b$ at scale $\lambda$ whose six chord owners are confined, whose floor owners are confined, and for which the smaller-height conclusions hold. The regional players are the six chord owners and the external users of the gadget region. Then:
--
--   1. a floor segment of nominal cost $s$ used by $r$ regional players charges each of them at least $\lambda s/(r+1)$ on the region of its seven units;
--   2. a nonowner traversing a shifted chord ($B$ with pendant $Y$, or $C$ with pendant $Z$) whose physical load is $m$ pays at least $\lambda y/m$, respectively $\lambda z/m$, on the chord and its pendant together;
--   3. a direct shifted owner pays only her physical chord share $\lambda(y-L_y)/m$, respectively $\lambda(z-L_z)/m$;
--   4. a nondirect shifted owner's direct return gains at least
--   $$
--   \bigl(\text{her payment outside the pendant region}\bigr)-\lambda y+\tfrac32\lambda L_y,
--   $$
--   respectively with $z,L_z$: the effective-cost return comparison plus the additional $3\lambda L_y/2$.
--
--   These are the prices the local comparison uses for abandoned pieces; they hold at every recursive height because of the smaller-height crossing bounds.
--
--   **Formalization Note** "Used by" a segment means that the player's path contains an edge of the segment's region. The effective chord coordinates $y,z$ include the pendant cost.
--
--   Differences from the source:
--   - reading: the gain "relative to the projected effective-cost return formula" → the gain is at least the owner's actual payment outside the pendant region minus $\lambda y$ plus $3\lambda L_y/2$; reason: formula (11) is a lower bound on that payment by the load counts of the finite trace, and the proof establishes exactly the stated inequality, which implies the printed one
--   - reading: "Floor confinement and the smaller-height conclusions are available" → the gadget's floor owners are confined and the smaller-height conclusions hold for the block; reason: the setting paragraph before Lemma A.4 (p.15); confinement is assumed only for the gadget under consideration, the stronger lemma
--   - encoding: a segment "used by $r$ regional players" charging each → $r$ counts the regional players whose path meets the segment's region, and the charge is the payment inside that region; reason: the unit regions $D(e)$ of the seven units carry the charge, as in the proof
--   - encoding: the parameters of the construction → $\eta(t)=(1-t)\eta_0+t\eta_1$ with $t$ rational and $0\le t<1$; reason: §A.5, p.18 (PDF p.20): "Throughout the construction use η(t) = (1 − t)η0 + tη1, where t is rational and 0 ≤ t < 1"
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), Lemma A.5, p.15 (PDF p.17)

import Mathlib
import Definitions.Def_PoSUndirected_gadgetRegion

open CongestionPoA.AsymSum PriceOfStability.Harmonic

namespace PoSUndirected

/-- Tsoufis (preprint, sha256 c095d811…), Lemma A.5 (Incumbent payments), p.15 (PDF p.17). Fix the
construction at `η(t)`, `0 ≤ t < 1` rational, of finite depth `d`, a weak equilibrium `A`, and a
gadget `g` of block `b` (scale `λ`) whose chord owners are confined, with floor confinement for its
floor units and the smaller-height conclusions available. The regional players are the six chord
owners and the external users of the gadget region. Then:

1. a floor segment of nominal cost `s` used by `r` regional players charges each at least
   `λs/(r + 1)` (on the region of its seven units and their descendants);
2. a nonowner traversing a shifted chord (`B` with pendant `Y`, or `C` with pendant `Z`) of
   physical load `m` pays at least `λy/m`, respectively `λz/m`, on the chord and pendant together;
3. a direct shifted owner pays only her physical chord share;
4. a nondirect shifted owner's direct return gains at least her payment outside the pendant
   region minus `λy` (respectively `λz`) plus the additional `3λL_y/2` (respectively `3λL_z/2`).

**Formalization Note.** Clause 4 is formalized with the owner's actual payment outside the pendant
in place of the "projected effective-cost return formula" (11), which bounds that payment from
below by load counts of the finite trace; the stated form implies the printed one. -/
theorem lemma_A_5_incumbent_payments (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) (d : ℕ)
    (A : HEdge d → Finset (HEdge d)) (hA : IsPureNash (hostGame (etaAt t) d) A) (b : HBlock d)
    (g : Fin 7) (hchord : ∀ κ, A (HEdge.chord b.1 b.2 g κ) ⊆ gadgetRegion b g)
    (hfloor : ∀ σ u, A (HEdge.floor b.1 b.2 g σ u) ⊆ unitRegion b.1 b.2 g σ u)
    (hsmall : SmallerHeightConcl (etaAt t) A b) :
    (∀ σ : Fin 13, ∀ i ∈ (regionalPlayers A b g).filter (fun j => (A j ∩ segRegion b g σ).Nonempty),
      ((lam (etaAt t) b.1 b.2 * (etaAt t).nominal σ : ℚ) : ℝ) /
          (((regionalPlayers A b g).filter (fun j => (A j ∩ segRegion b g σ).Nonempty)).card + 1) ≤
        payIn (hostGame (etaAt t) d) A i (segRegion b g σ)) ∧
    (∀ (κ : Fin 6) (σ : Fin 13) (Leff Lp : ℚ),
      (κ = 1 ∧ σ = 11 ∧ Leff = (etaAt t).y ∧ Lp = (etaAt t).Ly) ∨
        (κ = 2 ∧ σ = 12 ∧ Leff = (etaAt t).z ∧ Lp = (etaAt t).Lz) →
      (∀ i, i ≠ HEdge.chord b.1 b.2 g κ → HEdge.chord b.1 b.2 g κ ∈ A i →
        ((lam (etaAt t) b.1 b.2 * Leff : ℚ) : ℝ) / (load A (HEdge.chord b.1 b.2 g κ) : ℝ) ≤
          payIn (hostGame (etaAt t) d) A i (insert (HEdge.chord b.1 b.2 g κ) (segRegion b g σ))) ∧
      (A (HEdge.chord b.1 b.2 g κ) = {HEdge.chord b.1 b.2 g κ} →
        cost (hostGame (etaAt t) d) A (HEdge.chord b.1 b.2 g κ) =
          (hostCost (etaAt t) (HEdge.chord b.1 b.2 g κ) : ℝ) /
            (load A (HEdge.chord b.1 b.2 g κ) : ℝ)) ∧
      (A (HEdge.chord b.1 b.2 g κ) ≠ {HEdge.chord b.1 b.2 g κ} →
        payIn (hostGame (etaAt t) d) A (HEdge.chord b.1 b.2 g κ)
              (Finset.univ \ segRegion b g σ) -
            ((lam (etaAt t) b.1 b.2 * Leff : ℚ) : ℝ) +
            3 * ((lam (etaAt t) b.1 b.2 * Lp : ℚ) : ℝ) / 2 ≤
          cost (hostGame (etaAt t) d) A (HEdge.chord b.1 b.2 g κ) -
            cost (hostGame (etaAt t) d)
              (Function.update A (HEdge.chord b.1 b.2 g κ) {HEdge.chord b.1 b.2 g κ})
              (HEdge.chord b.1 b.2 g κ))) := by sorry

end PoSUndirected
