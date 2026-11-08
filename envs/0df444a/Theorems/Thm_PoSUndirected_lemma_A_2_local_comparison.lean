-- Prove2me | Theorems.Thm_PoSUndirected_lemma_A_2_local_comparison
-- name    : PoSUndirected.lemma_A_2_local_comparison
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T08:00:43.759235+00:00
-- url     : https://prove2.me/theorems/88ea3a23-17a3-4f31-862e-b1b770a35f68
-- title:
--   Lemma A.2 — local comparison in a confined gadget
-- statement:
--   Consider the host of finite depth $d$ at $\eta(t)$, $0\le t<1$ rational, a weak equilibrium $A$, and a gadget, at any height, of a block $b$ at scale $\lambda$, whose six chord owners are confined to the gadget. Suppose that the smaller-height blocks have confined owners and charge each of their $r\ge1$ external users more than their ceiling cost divided by $r$. Let $q$ be the number of external users of the gadget region. Then:
--
--   1. if $q=0$, all six chord owners are direct;
--   2. if $q\ge1$, each external user pays more than $\lambda\alpha/q$ inside the gadget region.
--
--   This is the finite core of the lower bound: it is what the six-chord gadget and the parameters of Appendix A.5 were chosen for, and its proof in the paper is the complete case analysis of Appendix F.
--
--   Differences from the source:
--   - encoding: "a confined gadget" → its six chord owners route inside the gadget region; reason: the definition at the start of §A.6 (p.20)
--   - encoding: smaller-height blocks → every block of greater depth in the depth-$d$ host, in the same profile; reason: height $=d-$depth
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), Lemma A.2, p.14 (PDF p.16); proof in §A.6 and Appendix F

import Mathlib
import Definitions.Def_PoSUndirected_gadgetRegion

open CongestionPoA.AsymSum PriceOfStability.Harmonic

namespace PoSUndirected

/-- Tsoufis (preprint, sha256 c095d811…), Lemma A.2 (Local comparison), p.14 (PDF p.16). Fix the
construction at `η(t)`, `0 ≤ t < 1` rational, of finite depth `d`, a weak equilibrium `A`, and a
gadget `g` of block `b` (any height, scale `λ`) whose six chord owners are confined to the gadget.
Suppose the smaller-height blocks have confined owners and charge each of their `r ≥ 1` external
users more than their ceiling cost divided by `r`. Let `q` be the number of external users of the
gadget region. If `q = 0`, all six chord owners are direct; if `q ≥ 1`, each external user pays
more than `λα/q` inside the gadget region.

**Formalization Note.** "Confined gadget" means its six chord owners are confined (§A.6, p.20
(PDF p.22)). The smaller-height hypothesis is `SmallerHeightConcl`, about the same profile `A`. -/
theorem lemma_A_2_local_comparison (t : ℚ) (ht0 : 0 ≤ t) (ht1 : t < 1) (d : ℕ)
    (A : HEdge d → Finset (HEdge d)) (hA : IsPureNash (hostGame (etaAt t) d) A) (b : HBlock d)
    (g : Fin 7) (hchord : ∀ κ, A (HEdge.chord b.1 b.2 g κ) ⊆ gadgetRegion b g)
    (hsmall : SmallerHeightConcl (etaAt t) A b) :
    ((extUsers A (gadgetRegion b g)).card = 0 →
      ∀ κ, A (HEdge.chord b.1 b.2 g κ) = {HEdge.chord b.1 b.2 g κ}) ∧
    (∀ i ∈ extUsers A (gadgetRegion b g),
      ((lam (etaAt t) b.1 b.2 * (etaAt t).α : ℚ) : ℝ) / (extUsers A (gadgetRegion b g)).card <
        payIn (hostGame (etaAt t) d) A i (gadgetRegion b g)) := by sorry

end PoSUndirected
