-- Prove2me | Theorems.Thm_PoSUndirected_eq_5_limit
-- name    : PoSUndirected.eq_5_limit
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:58:10.381203+00:00
-- url     : https://prove2.me/theorems/6149a076-6ce6-42b6-b0f5-f8d92ccd5bc5
-- title:
--   Equation (5) — $L-\mathcal L(\eta(t))=(1-t)K_0/((1-t)D_0+t)$ and $\mathcal L(\eta_1)=L$
-- statement:
--   At the endpoint $\eta_1$:
--   $$
--   S-\alpha=1,\quad S=\frac{3970769424343}{3195649632469},\quad C_\Sigma=\frac{3837588754646}{3195649632469},\quad S_{\rm rec}=\frac{1733801419330}{3195649632469},\quad \mathcal L(\eta_1)=L .
--   $$
--   At $\eta_0$, $D_0=S-\alpha=1090675263063651/1210025397060928$ and $K_0=D_0\,(L-\mathcal L(\eta_0))>0$. For every rational $0\le t\le1$,
--   $$
--   L-\mathcal L(\eta(t))=\frac{(1-t)K_0}{(1-t)D_0+t}.\tag{5}
--   $$
--
--   Here $L=7808358178989/3195649632469$ is the constant of Theorem 3.1 and $\mathcal L(\eta)=(S+C_\Sigma)/(S-\alpha)$. Equation (5) shows that $\mathcal L(\eta(t))$ approaches $L$ from below as $t\to1$, which supplies the first half of the $\varepsilon$ in the main theorem.
--
--   Differences from the source:
--   - generalization: equation (5) on the construction's range $0\le t<1$ → $0\le t\le1$; reason: the closed segment contains the source's range (both sides vanish at $t=1$)
-- source:
--   Tsoufis, The Price of Stability in Undirected Network Design: Lower Bounds and Structural Guarantees (preprint, sha256 c095d811fa04b471d74ba4fdab8fb89ccb3d34079d3bf07384f46ac57144866c), §A.4, equation (5), p.18 (PDF p.20)

import Mathlib
import Definitions.Def_PoSUndirected_Params

namespace PoSUndirected

open Params in
/-- Tsoufis (preprint, sha256 c095d811…), §A.4, p.18 (PDF p.20), equation (5) and the values at
`η₁`. At `η₁`: `S − α = 1`, `S = 3970769424343/3195649632469`, `C_Σ = 3837588754646/3195649632469`,
`S_rec = 1733801419330/3195649632469` and `L(η₁) = L`. At `η₀`:
`D₀ = S − α = 1090675263063651/1210025397060928 > 0` and `K₀ = D₀(L − L(η₀)) > 0`. For every rational
`0 ≤ t ≤ 1`, `L − L(η(t)) = (1 − t)K₀/((1 − t)D₀ + t)`.

**Formalization Note.** `L` is the constant `Lconst` of Theorem 3.1 and `L(η) = (S + C_Σ)/(S − α)`
is `Params.Leta`. Equation (5) is stated on the closed segment `0 ≤ t ≤ 1` (at `t = 1` both sides
vanish). -/
theorem eq_5_limit :
    eta1.S - eta1.α = 1 ∧ eta1.S = 3970769424343 / 3195649632469 ∧
    eta1.CSigma = 3837588754646 / 3195649632469 ∧ eta1.Srec = 1733801419330 / 3195649632469 ∧
    eta1.Leta = Lconst ∧ eta0.S - eta0.α = 1090675263063651 / 1210025397060928 ∧
    0 < (eta0.S - eta0.α) * (Lconst - eta0.Leta) ∧
    ∀ t : ℚ, 0 ≤ t → t ≤ 1 →
      Lconst - (etaAt t).Leta = (1 - t) * ((eta0.S - eta0.α) * (Lconst - eta0.Leta)) /
        ((1 - t) * (eta0.S - eta0.α) + t) := by sorry

end PoSUndirected
