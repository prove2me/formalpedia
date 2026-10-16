-- Prove2me | Theorems.Thm_StrategicAlloc_RRFair_restriction_best_response
-- name    : StrategicAlloc.RRFair.restriction_best_response
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:57:51.247054+00:00
-- url     : https://prove2.me/theorems/78286750-f5f6-4cfc-9790-aa449d47fa21
-- title:
--   Proof of Theorem 3.3, p. 10 — at a PNE, agent $\ell$'s bid is a best response in Round-Robin$_\ell$ on $M\setminus H$
-- statement:
--   Let $v_1,\dots,v_n$ be non-negative additive valuations and $b$ a pure Nash equilibrium of Round-Robin. Let $\ell\ge2$, let $H=\{h_1,\dots,h_{\ell-1}\}$ be the goods taken by agents $1,\dots,\ell-1$ in the first round, and $M'=M\setminus H$. Then the restricted bid $b'_\ell=b_\ell|_{M'}$ is a best response of agent $\ell$ in Round-Robin$_\ell$ on $M'$ (turn order $\ell,\dots,n,1,\dots,\ell-1$) when the restricted bids of all other agents are fixed: for every non-negative bid vector $c$,
--   $$v_\ell\big(\text{Round-Robin}_\ell(c|_{M'},b'_{-\ell})_\ell\big)\ \le\ v_\ell\big(\text{Round-Robin}_\ell(b')_\ell\big).$$
--
--   This lets Theorem 3.4 be applied with agent $\ell$ in the role of the first mover.
--
--   **Formalization Note.** Agents are `Fin n` and goods `Fin m`, both 0-based (the paper's agent $i$ is $i-1$, good $g_j$ is $j-1$, and the paper's step $t$ is $t-1$). Agent $\ell$ is the 0-based `ℓ` with `0 < ℓ`, $H$ is `allocBefore 0 univ b ℓ`, Round-Robin$_\ell$ on $M'$ is `rrFrom ℓ (univ \ H)` (with the wrap-around the page omits). Values are measured with $v_\ell$, which on bundles inside $M'$ is the restricted valuation $v'_\ell$ of the page.
-- source:
--   Amanatidis et al., Allocating Indivisible Goods to Strategic Agents, arXiv:2109.08644v2, p. 10, proof of Theorem 3.3, second paragraph

import Mathlib
import Definitions.Def_StrategicAlloc_RRFair_Setting

namespace StrategicAlloc.RRFair

variable {n m : ℕ}

/-- Proof of Theorem 3.3 (p. 10), the best-response transfer: at a PNE of Round-Robin, agent
`ℓ`'s bid is a best response in Round-Robin started at `ℓ` on the goods `M \ H`. -/
theorem restriction_best_response [NeZero n] (v : Fin n → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (b : Fin n → Fin m → ℝ) (hpne : IsPNE roundRobin v b) (ℓ : Fin n) (hℓ : 0 < ℓ) :
    IsBestResponse (rrFrom ℓ (Finset.univ \ allocBefore 0 Finset.univ b ℓ)) v b ℓ := by sorry

end StrategicAlloc.RRFair
