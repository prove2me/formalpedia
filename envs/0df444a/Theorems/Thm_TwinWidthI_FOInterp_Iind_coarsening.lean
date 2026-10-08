-- Prove2me | Theorems.Thm_TwinWidthI_FOInterp_Iind_coarsening
-- name    : TwinWidthI.FOInterp.Iind_coarsening
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:45:27.393066+00:00
-- url     : https://prove2.me/theorems/9373f801-e26d-49e6-8947-85d7fea31076
-- title:
--   §8, p. 3:42 — I_{ℓ+2}(G, P) refines P, and coarsening P coarsens I_{ℓ+2}(G, P)
-- statement:
--   Let $G$ be a finite simple graph, $\ell\ge 0$, and $\mathcal P,\mathcal P'$ partitions of $V(G)$. Then:
--   1. $I_{\ell+2}(G,\mathcal P)$ refines $\mathcal P$: two vertices in the same connected component of $E_{\ell+2}(G,\mathcal P)$ lie in the same part of $\mathcal P$;
--   2. if $\mathcal P'$ is a coarsening of $\mathcal P$, every edge of $E_{\ell+2}(G,\mathcal P)$ is an edge of $E_{\ell+2}(G,\mathcal P')$;
--   3. consequently, if $\mathcal P'$ is a coarsening of $\mathcal P$, then $I_{\ell+2}(G,\mathcal P')$ is a coarsening of $I_{\ell+2}(G,\mathcal P)$: vertices in the same component of $E_{\ell+2}(G,\mathcal P)$ are in the same component of $E_{\ell+2}(G,\mathcal P')$.
--
--   Along a sequence of $d$-partitions $\mathcal P_n,\dots,\mathcal P_1$ this makes the partitions $I_{\ell+2}(G,\mathcal P_i)$ a nested sequence, which is what the proof of Theorem 8.3 refines.
--
--   **Formalization Note.** $I_{\ell+2}(G,\mathcal P)$ is represented by connectivity (`Reachable`) in `Eind G P (ℓ + 2)`; "$\mathcal P'$ is a coarsening of $\mathcal P$" is `P ≤ P'` in Mathlib's order on finite partitions (every part of $\mathcal P$ lies in a part of $\mathcal P'$).
-- source:
--   Bonnet, Kim, Thomassé and Watrigant, Twin-width I: Tractable FO Model Checking, J. ACM 69(1), Article 3 (2021), p. 3:42, §8, "Note that I_{ℓ+2}(G, P) refines P, and that if P′ is a coarsening of P then I_{ℓ+2}(G, P′) is also a coarsening of I_{ℓ+2}(G, P)"

import Mathlib
import Definitions.Def_TwinWidthI_FOInterp_Setting
import Definitions.Def_TwinWidthI_FOInterp_MorphismTree

namespace TwinWidthI.FOInterp

open Finset

theorem Iind_coarsening {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P P' : Finpartition (univ : Finset V)) (ℓ : ℕ) :
    (∀ u u' : V, (Eind G P (ℓ + 2)).Reachable u u' → P.part u = P.part u') ∧
    (P ≤ P' → ∀ u u' : V, (Eind G P (ℓ + 2)).Adj u u' → (Eind G P' (ℓ + 2)).Adj u u') ∧
    (P ≤ P' → ∀ u u' : V, (Eind G P (ℓ + 2)).Reachable u u' →
      (Eind G P' (ℓ + 2)).Reachable u u') := by sorry

end TwinWidthI.FOInterp
