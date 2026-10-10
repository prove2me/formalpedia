-- Prove2me | Theorems.Thm_RunIntersect_Tight_mp_eq_proj_mp_gplus
-- name    : RunIntersect.Tight.mp_eq_proj_mp_gplus
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:29.50597+00:00
-- url     : https://prove2.me/theorems/065e4e70-ef16-4873-866e-1d174be4e7bf
-- title:
--   §5.3.1, p. 1035 — projecting out z_p̄ from MP_{G⁺} gives MP_G
-- statement:
--   Let $G=(V,E)$ be a kite-free β-acyclic hypergraph with $\kappa\ge 2$ maximal edges, $\mathcal O$ a running intersection ordering of them, $\tilde e$ the last one, $\bar p=N(\tilde e)$, and suppose $|\bar p|\ge 2$ and $\bar p\notin E$, so that $G^+=(V,E\cup\{\bar p\})$. Then $\mathrm{MP}_G$ is obtained from $\mathrm{MP}_{G^+}$ by projecting out the auxiliary variable $z_{\bar p}$:
--   $$\mathrm{MP}_G=\{\,z \text{ with } z_{\bar p}\text{ set to } 0 : z\in\mathrm{MP}_{G^+}\}.$$
--
--   This reduces the original-space characterization to a Fourier–Motzkin elimination of one variable.
--
--   **Formalization Note** Projection is the map that sets the coordinate $z_{\bar p}$ to $0$ (the coordinate is not one of $G$, where every point vanishes). The cases $|\bar p|\le 1$ or $\bar p\in E$ are the page's "$G=G^+$" branch and are excluded here, as on the page ("Henceforth, assume that $\bar p\notin V\cup E$"). No hypothesis on isolated nodes is needed.
-- source:
--   Del Pia and Khajavirad, The running intersection relaxation of the multilinear polytope, Math. Oper. Res. 46 (2021), p. 1035, §5.3.1 (proof of Theorem 3), last paragraph

import Mathlib
import Definitions.Def_RunIntersect_Tight_Setting

namespace RunIntersect.Tight

theorem mp_eq_proj_mp_gplus {α : Type*} [Fintype α] [DecidableEq α]
    (G : Hypergraph α) (hkite : IsKiteFree G) (hβ : IsBetaAcyclic G)
    (O : List (Finset α)) (hOnd : O.Nodup) (hO : O.toFinset = maxEdges G) (hOri : IsRIOrder O)
    (hκ : 2 ≤ O.length)
    (hp : 2 ≤ (pbar O).card) (hpE : pbar O ∉ G.E) :
    MP G = (fun z => Function.update z (Sum.inr (pbar O)) 0) '' MP (GplusLast G O) := by sorry

end RunIntersect.Tight
