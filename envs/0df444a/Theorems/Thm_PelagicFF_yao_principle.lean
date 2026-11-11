-- Prove2me | Theorems.Thm_PelagicFF_yao_principle
-- name    : PelagicFF.yao_principle
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:55:49.23799+00:00
-- url     : https://prove2.me/theorems/c88681b8-1e7f-4699-ba6a-04a0b5eff476
-- title:
--   §4.2.2, p.30 — Yao's principle (averaging direction)
-- statement:
--   Let $P$ be a randomized public-coin two-way protocol, $R$ a relation, $\mu$ a probability law on inputs $X\times Y$ and $p\in\mathbb R$. If the success probability of $P$ averaged over $(x,y)\sim\mu$ is at least $p$, then there is a coin value $r$ of positive probability such that the deterministic protocol $P_r$ run on coin $r$ has depth at most the cost of $P$ and
--   $$\Pr_{(x,y)\sim\mu}\big[P_r(x,y)\in R(x,y)\big]\ \ge\ p .$$
--
--   This is how the lower bound of Theorem 4.2 reduces to deterministic protocols of the same cost on the uniform input distribution.
--
--   **Formalization Note** Stated for every input law $\mu$; the uniform law is the case the proof uses.
--
--   Differences from the source:
--   - reading: "By Yao's principle [Yao83], it suffices to show that all deterministic protocols using c = o(N) bits … succeed with probability less than 2/3 under a hard input distribution" → the averaging direction: a public-coin protocol of μ-average success ≥ p runs, on some coin of positive probability, a deterministic tree of depth ≤ cost with μ-average success ≥ p; reason: this is the direction of Yao's principle the argument uses
--   - generalization: the hard input distribution (uniform truth tables) → every input law μ on X × Y; reason: taking μ uniform gives the case used
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), §4.2.2, p.30

import Mathlib
import Definitions.Def_PelagicFF_PubCoinProtocol

open Classical

namespace PelagicFF

/-- **Yao's principle, the direction used (§4.2.2, p.30).** If a public-coin protocol succeeds with
probability at least `p` on average under an input law `μ`, then for some coin value `r` of positive
probability the deterministic protocol `P.tree r` (of depth at most the cost of `P`) succeeds with
probability at least `p` on average under `μ`.

arXiv:2610.05585 (held version, sha256 4564aef3…), §4.2.2, p.30: "By Yao's principle [Yao83], it
suffices to show that all deterministic protocols using c = o(N) bits of communication succeed with
probability less than 2/3 under a hard input distribution, for all sufficiently large n."

**Formalization Note.** Stated for every input law `μ` on `X × Y`; the proof of Theorem 4.2 uses the
uniform law. -/
theorem yao_principle {X Y Z : Type} [Fintype X] [Fintype Y] (P : PubCoinProtocol X Y Z)
    (R : X → Y → Z → Prop) (μ : PMF (X × Y)) (p : ℝ)
    (hp : p ≤ ∑ xy, (μ xy).toReal * P.succProb R xy.1 xy.2) :
    ∃ r, P.coin r ≠ 0 ∧ (P.tree r).depth ≤ P.cost ∧
      p ≤ ∑ xy, (μ xy).toReal *
        (if R xy.1 xy.2 ((P.tree r).eval xy.1 xy.2 xy.2) then 1 else 0) := by sorry

end PelagicFF
