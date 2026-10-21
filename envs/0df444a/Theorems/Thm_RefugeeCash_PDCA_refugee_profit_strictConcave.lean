-- Prove2me | Theorems.Thm_RefugeeCash_PDCA_refugee_profit_strictConcave
-- name    : RefugeeCash.PDCA.refugee_profit_strictConcave
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:45:36.101351+00:00
-- url     : https://prove2.me/theorems/f8e5f2c0-065e-4711-baad-955a30054dbd
-- title:
--   §6.3, p. 22 (PDF 23) — where k(p) ∈ (0,1), the refugee profit k(p)B(1 − c/p) under the PDCA scheme is strictly concave in p
-- statement:
--   In the symmetric-goods model with $B > 0$, $c > 0$ and Assumption 2 (with maximizer $p_0$ of $\pi_0$), take a target $c < p^\odot \le p_0$ and $k^\odot \in [0,1]$, and let $k(p)$ be the PDCA scheme (27). On the set of prices
--   $$I = \{\, p > c \;:\; 0 < k(p) < 1 \,\},$$
--   the retailer's profit from the refugees,
--   $$p \longmapsto \pi_r\big(p, k(p)\big) = k(p)\,B\Big(1 - \frac{c}{p}\Big),$$
--   is strictly concave.
--
--   Strict concavity of this branch is one ingredient of the paper's conclusion that the retailer's profit under the PDCA scheme is piecewise concave over the whole price range.
--
--   **Formalization Note** The page says this "can be readily seen". It holds because the slope $S(p^\odot,k^\odot)$ is non-positive, which uses $p^\odot \le p_0$ (the paper's reading of the residents' constraint $C(p) \ge C(p_0)$ in (26), p. 21) and Assumption 2; with a positive slope the claim can fail. These two hypotheses are therefore stated. The set $I$ may be empty (for instance when $k^\odot = 0$ and the slope is $0$), in which case the claim is trivially true.
-- source:
--   Kotsi, Wu & Pedraza-Martinez, Donations for Refugee Crises: In-kind Versus Cash Assistance, manuscript of November 27, 2021 (MSOM, DOI 10.1287/msom.2021.1073), p. 22 (PDF 23), §6.3, paragraph after eq. (27); constraint p* ≤ p0, p. 21 (PDF 22)

import Mathlib
import Definitions.Def_RefugeeCash_PDCA_Model

namespace RefugeeCash.PDCA

/-- §6.3, p. 22 (PDF 23): on the prices `p > c` with `k(p) ∈ (0, 1)`, the retailer's profit from
the refugees under the PDCA scheme (27), `k(p) B (1 − c/p)`, is strictly concave in `p`, for a
target `c < p⊙ ≤ p0`, `k⊙ ∈ [0, 1]`. -/
theorem refugee_profit_strictConcave (P : Params) (hP : P.Standing) (pmax p0 : ℝ)
    (hA2 : Assumption2 P pmax p0) (pT kT : ℝ) (hpT : P.c < pT) (hpT0 : pT ≤ p0)
    (hkT : kT ∈ Set.Icc (0 : ℝ) 1) :
    StrictConcaveOn ℝ {p | P.c < p ∧ 0 < kPDCA P pT kT p ∧ kPDCA P pT kT p < 1}
      (fun p => piR P p (kPDCA P pT kT p)) := by sorry

end RefugeeCash.PDCA
