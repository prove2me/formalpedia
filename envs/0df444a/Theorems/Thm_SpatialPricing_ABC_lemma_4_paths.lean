-- Prove2me | Theorems.Thm_SpatialPricing_ABC_lemma_4_paths
-- name    : SpatialPricing.ABC.lemma_4_paths
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T02:44:21.13999+00:00
-- url     : https://prove2.me/theorems/6710f779-20a3-40c8-a593-161b624f79ea
-- title:
--   Lemma 4 (sample paths), p. 25 — ABC keeps at least N servers and posts an interior target rate
-- statement:
--   Fix a standing spatial pricing instance whose minimum travel time satisfies $\underline\tau\le T$, and a scaling factor $n\ge1$. Use Theorem 3's parameters $b_n$, $\epsilon_n$, and $\zeta_n$, and set $\eta_n=(\epsilon_n\underline\tau^n-1)/4$. Suppose $\mathrm{DCP}(n,\zeta_n)$ is feasible and $2\eta_n/b_n<1$. On every positive-probability path in the batchwise good event $\mathcal A$, every region has at least $N$ available servers at every period. For each arc and period, ABC posts exactly the unprojected rate
--
--   $$\widehat\lambda_{t,ij}=\lambda^{n,\zeta,D}_{t,ij}-\epsilon_n-u_{t,ij}\bar\delta^{\kappa_{ij}(t)-1}_{ij}\in(0,1).$$
--
--   This identifies the control's actual rate on the event used by the ABC performance analysis.
--
--   **Formalization Note** Feasibility replaces C2's reference to $\bar\zeta>\zeta$: Lemma 2 supplies that implication. The price identity in the manuscript is expressed as equality of posted demand rates. The event and correction use the control's actual posted rates, and the ABC server test uses $\ge N$ to resolve the printed boundary slip. The hypothesis $\underline\tau\le T$ is not printed, and without it the lemma is false. If the horizon is shorter than every travel time, no server returns. For example, take $N=1$, $T=2$, $C_1=1$, $\tau_{11}=31623$, $r(\lambda)=\lambda(1-\lambda)$ and $n=1$. Then C2 holds and DCP is feasible, but a realized trip in period 1 leaves $C_{2,1}=0<N$ on a path in $\mathcal A$. The proof's bound $C^n_{t+1,i}\ge N\epsilon\underline\tau^n-4N\eta$ (EC.10)–(EC.11) needs $\underline\tau^n\le T^n$.
-- source:
--   Chen, Lei, Jasin, accepted manuscript, LBS Research Online eprint 2845, PDF sha256 7310a8a1…480a, pp. 24–25, C2, event A, Lemma 4 (PDF 25–26)

import Mathlib
import Definitions.Def_SpatialPricing_ABC_Setting
import Definitions.Def_SpatialPricing_ABC_Control

namespace SpatialPricing.ABC

/-- Lemma 4, p. 25: availability and unprojected target rates on the good event.
The hypothesis `hτT : τ̲ ≤ T` is not printed: without it the lemma is false (a horizon shorter
than every travel time returns no server, and one realized trip from a node with `C_{1,i} = N`
leaves `C_{2,i} < N` on a path in `A`). The proof (EC.10) uses it through the bound `N ϵ τ̲ⁿ`. -/
theorem lemma_4_paths (P : Instance) (Ψ3 : ℝ) (hP : P.Standing Ψ3)
    (hτT : P.tauMin ≤ P.T)
    (n : ℕ) (hn : 1 ≤ n)
    (hfeas : ∃ x, (P.scale n).DCPFeasible (P.zetaN n) x)
    (hC2 : 2 * P.etaN n / P.bN n < 1) :
    ∀ ω : (P.scale n).Path,
      0 < (P.scale n).pathProb
        ((P.scale n).abcRate (P.epsN n) (P.zetaN n) (P.bN n)) ω →
      (P.scale n).inA (P.epsN n) (P.zetaN n) (P.bN n) (P.etaN n) ω →
      ∀ t ∈ Finset.Icc 1 (P.scale n).T,
        (∀ i, ((P.scale n).N : ℝ) ≤ (P.scale n).avail t ω i) ∧
        ∀ i j,
          let target := (P.scale n).lamD (P.zetaN n) t i j - P.epsN n -
            (P.scale n).u (P.zetaN n) (P.bN n) t i j *
              (P.scale n).deltaPrev (P.epsN n) (P.zetaN n) (P.bN n) t ω i j
          (P.scale n).abcRate (P.epsN n) (P.zetaN n) (P.bN n) t ω i j = target ∧
            0 < target ∧ target < 1 := by sorry

end SpatialPricing.ABC
