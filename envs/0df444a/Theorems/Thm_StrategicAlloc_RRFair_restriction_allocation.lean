-- Prove2me | Theorems.Thm_StrategicAlloc_RRFair_restriction_allocation
-- name    : StrategicAlloc.RRFair.restriction_allocation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:57:58.91311+00:00
-- url     : https://prove2.me/theorems/768c41ae-e417-4211-a937-f34b0ccbd9df
-- title:
--   Proof of Theorem 3.3, p. 10 — Round-Robin returns $(A_1\cup\{h_1\},\dots,A_{\ell-1}\cup\{h_{\ell-1}\},A_\ell,\dots,A_n)$
-- statement:
--   Let $b$ be a bid profile and $\ell\ge2$. Let $h_1,\dots,h_{\ell-1}$ be the goods taken by agents $1,\dots,\ell-1$ in the first round of Round-Robin$(b)$, $H=\{h_1,\dots,h_{\ell-1}\}$, and let $(A_1,\dots,A_n)$ be the allocation returned by Round-Robin$_\ell$ on $M'=M\setminus H$ (turn order $\ell,\dots,n,1,\dots,\ell-1$) with the restricted bids. Then Round-Robin$(b)$ returns the allocation
--   $$(A_1\cup\{h_1\},\ \dots,\ A_{\ell-1}\cup\{h_{\ell-1}\},\ A_\ell,\ \dots,\ A_n).$$
--
--   With Theorem 3.4 for the restricted run this gives, for $i<\ell$, $v_\ell(A_\ell)\ge v_\ell((A_i\cup\{h_i\})\setminus\{h_i\})$, which is EF1 from agent $\ell$'s perspective.
--
--   **Formalization Note.** Agents are `Fin n` and goods `Fin m`, both 0-based (the paper's agent $i$ is $i-1$, good $g_j$ is $j-1$, and the paper's step $t$ is $t-1$). Agent $\ell$ is the 0-based `ℓ` with `0 < ℓ`; $H$ is `allocBefore 0 univ b ℓ` and $h_j$ is `pick 0 univ b j`, the good allocated at step $j$ (absent if $m\le j$, in which case nothing is added). Round-Robin$_\ell$ on $M'$ is `rrFrom ℓ (univ \ H)`, with the wrap-around the page omits.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 10, proof of Theorem 3.3, third paragraph

import Mathlib
import Definitions.Def_StrategicAlloc_RRFair_Setting

namespace StrategicAlloc.RRFair

variable {n m : ℕ}

/-- Proof of Theorem 3.3 (p. 10): with `H = {h_1, …, h_{ℓ−1}}` the goods taken by agents
`0, …, ℓ − 1` in the first round, Round-Robin's allocation is the allocation of Round-Robin
started at `ℓ` on `M \ H`, with `h_j` added to the bundle of each agent `j < ℓ`. -/
theorem restriction_allocation [NeZero n] (b : Fin n → Fin m → ℝ) (hb : IsBidProfile b)
    (ℓ : Fin n) (hℓ : 0 < ℓ) (j : Fin n) :
    roundRobin b j =
      rrFrom ℓ (Finset.univ \ allocBefore 0 Finset.univ b ℓ) b j ∪
        (if j < ℓ then (pick 0 Finset.univ b j).toFinset else ∅) := by sorry

end StrategicAlloc.RRFair
