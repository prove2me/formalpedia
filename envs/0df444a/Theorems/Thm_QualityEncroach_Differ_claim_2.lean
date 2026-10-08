-- Prove2me | Theorems.Thm_QualityEncroach_Differ_claim_2
-- name    : QualityEncroach.Differ.claim_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:19.127649+00:00
-- url     : https://prove2.me/theorems/13316c5c-dc0c-4f4e-a9f5-ffe608d410ce
-- title:
--   Claim 2, p. 32 — a threshold c₂ > 0 such that the manufacturer encroaches when c < c₂ and does not when c > c₂
-- statement:
--   Fix $k>0$ and consider the encroachment game with quality differentiation (§5). There is a threshold $c_2>0$, depending only on $k$, such that for every direct selling cost $c\ge0$ an equilibrium exists and every subgame-perfect equilibrium satisfies:
--
--   1. if $c<c_2$, the manufacturer encroaches: $q^*_M>0$ on the equilibrium path;
--   2. if $c>c_2$, she does not: $q^*_M=0$ on the equilibrium path.
--
--   This is the encroachment threshold of Table 1.
--
--   **Formalization Note.** The page reads "if and only if $c\le c_2\approx0.1019/k$". The numerical value is an approximation and is not stated. The boundary point $c=c_2$ is left out: Claim 2 and Table 1 include it in the encroachment region, while Proposition 1(i), whose threshold $\tilde c$ the proof identifies with $c_2$, excludes it.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 32, Claim 2 (proof: pp. 34–35)

import Mathlib
import Definitions.Def_QualityEncroach_Differ_Game

namespace QualityEncroach.Differ

theorem claim_2 (k : ℝ) (hk : 0 < k) :
    ∃ c2 : ℝ, 0 < c2 ∧
      ∀ c : ℝ, 0 ≤ c →
        (∃ σ : Profile, IsSPE k c (Set.Ioi 0) σ) ∧
        ∀ σ : Profile, IsSPE k c (Set.Ioi 0) σ →
          (c < c2 → 0 < σ.path.qM) ∧ (c2 < c → σ.path.qM = 0) := by sorry

end QualityEncroach.Differ
