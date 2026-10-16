-- Prove2me | Theorems.Thm_StrategicAlloc_RRFair_restriction_run
-- name    : StrategicAlloc.RRFair.restriction_run
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:57:43.954542+00:00
-- url     : https://prove2.me/theorems/2095580d-458e-4cd8-aa2c-f6fb4f5e1cdb
-- title:
--   Proof of Theorem 3.3, p. 10 — Round-Robin and Round-Robin$_\ell$ on $M\setminus H$ give agent $\ell$ the same bundle for every bid of hers
-- statement:
--   Let $b$ be a bid profile and $\ell\ge2$ an agent. For $i<\ell$ let $h_i$ be the good agent $i$ receives in the first round of Round-Robin$(b)$, and $H=\{h_1,\dots,h_{\ell-1}\}$, $M'=M\setminus H$. Let Round-Robin$_\ell$ be Round-Robin on the goods $M'$ with the turn order $\ell,\ell+1,\dots,n,1,\dots,\ell-1$. Then for every non-negative bid vector $c_\ell$ of agent $\ell$, the bundle agent $\ell$ receives from
--   $$\text{Round-Robin}(c_\ell,b_{-\ell})\quad\text{and from}\quad \text{Round-Robin}_\ell(c_\ell|_{M'},\,b'_{-\ell})$$
--   is the same, where $b'$ restricts the bids to $M'$.
--
--   Agents $1,\dots,\ell-1$ move before agent $\ell$ in the first round, so $H$ does not depend on agent $\ell$'s bid, and from step $\ell$ onward the two runs coincide.
--
--   **Formalization Note.** Agents are `Fin n` and goods `Fin m`, both 0-based (the paper's agent $i$ is $i-1$, good $g_j$ is $j-1$, and the paper's step $t$ is $t-1$). Agent $\ell$ is the 0-based `ℓ` with `0 < ℓ` (the paper's $\ell\ge2$). $H$ is `allocBefore 0 univ b ℓ`, the goods allocated in the first $\ell$ steps (fewer if $m<\ell$), and Round-Robin$_\ell$ on $M'$ is `rrFrom ℓ (univ \ H)`; it reads bids only on $M'$, which is the restriction $c_\ell|_{M'}$. The page's description of Round-Robin$_\ell$ omits the wrap-around from agent $n$ to agents $1,\dots,\ell-1$, who still pick in $M'$; the definition includes it.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 10, proof of Theorem 3.3, second paragraph

import Mathlib
import Definitions.Def_StrategicAlloc_RRFair_Setting

namespace StrategicAlloc.RRFair

variable {n m : ℕ}

/-- Proof of Theorem 3.3 (p. 10), the run identity for agent `ℓ`: with `H` the goods taken by
agents `0, …, ℓ − 1` in the first round, Round-Robin started at `ℓ` on `M \ H` gives agent `ℓ` the
same bundle as Round-Robin, whatever non-negative bid vector `c` she reports. -/
theorem restriction_run [NeZero n] (b : Fin n → Fin m → ℝ) (hb : IsBidProfile b)
    (ℓ : Fin n) (hℓ : 0 < ℓ) (c : Fin m → ℝ) (hc : ∀ g, 0 ≤ c g) :
    roundRobin (Function.update b ℓ c) ℓ =
      rrFrom ℓ (Finset.univ \ allocBefore 0 Finset.univ b ℓ) (Function.update b ℓ c) ℓ := by sorry

end StrategicAlloc.RRFair
