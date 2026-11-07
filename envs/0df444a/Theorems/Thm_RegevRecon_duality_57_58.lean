-- Prove2me | Theorems.Thm_RegevRecon_duality_57_58
-- name    : RegevRecon.duality_57_58
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:04:12.541934+00:00
-- url     : https://prove2.me/theorems/89af94c1-abb2-4ada-a1fe-637bde7fa249
-- title:
--   (57), (58) and the relabeling identity — channel duality for $\mathcal L$
-- statement:
--   Let $q,r$ be probability vectors on $\mathbb F_p$, and let $\mathcal L(q)$ be the random vector $z\mapsto q_{A-z}$, $A\sim q$. Let $w$ be the parity output of $(q,r)$: draw $s$ with probability $\pi_s=\sum_aq_ar_{a+s}$ and set $w_a=q_ar_{a+s}/\pi_s$. Then, with independent lifts on each right-hand side and as identities of joint vector distributions,
--
--   $$
--   \mathcal L(q*r)\overset d=\mathcal L(q)*\mathcal L(r),\qquad \mathcal L(w)_x\overset d=\frac{\mathcal L(q)_x\mathcal L(r)_x}{\sum_y\mathcal L(q)_y\mathcal L(r)_y},\qquad \mathcal L(R_\alpha q)_x\overset d=\mathcal L(q)_{\alpha x}.
--   $$
--
--   Under the lift, the two BPQM updates become the two updates of the reconstruction recursion. This is the core of the paper's duality.
--
--   Differences from the source:
--   - encoding: laws of random vectors, =d → finitely supported Law; =d is equality of masses at every whole vector; reason: all these vectors take finitely many values; same instances
-- source:
--   Jordan, Nguyen, Zhou, Regev's Reduction Reaches Reconstruction, STOC 2027 submission (manuscript sha256 9f861d6a…), (57), (58) and the relabeling identity, p.22

import Mathlib
import Definitions.Def_RegevRecon_Messages

namespace RegevRecon

open Filter Topology

/-- **Channel duality identities (57), (58) and the relabeling identity**. Jordan, Nguyen, Zhou, *Regev's Reduction Reaches Reconstruction*, STOC 2027 submission (manuscript sha256 9f861d6a…), p.22: for probability
vectors `q, r` on `F_p`, with `w` the parity output of (32) (draw `s` with probability `π_s`, set
`w_a = q_a r_{a+s}/π_s`), `𝓛(q ∗ r) =d 𝓛(q) ∗ 𝓛(r)`; `𝓛(w)_x =d 𝓛(q)_x 𝓛(r)_x / Σ_y 𝓛(q)_y 𝓛(r)_y`; and
`𝓛(R_α q)_x =d 𝓛(q)_{αx}`. "These are identities of joint vector distributions, with independent input
lifts on each right-hand side."

**Formalization Note** Each `=d` is equality of `Law`s on whole vectors; in (58) the left side is also
random in `s`. -/
theorem duality_57_58 {p : ℕ} [Fact p.Prime] (q r : Vec p) (hq : IsProbVec q) (hr : IsProbVec r) :
    liftVec (conv q r) =
        (liftVec q).bind (fun L₁ => (liftVec r).map fun L₂ => conv L₁ L₂) ∧
      (Law.ofWeights (parityProb q r) (parityVec q r)).bind liftVec =
        (liftVec q).bind (fun L₁ => (liftVec r).map fun L₂ x =>
          L₁ x * L₂ x / ∑ y, L₁ y * L₂ y) ∧
      ∀ α : (ZMod p)ˣ, liftVec (relabel (α : ZMod p) q) =
        (liftVec q).map fun L x => L ((α : ZMod p) * x) := by sorry

end RegevRecon
