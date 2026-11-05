-- Prove2me | Theorems.Thm_QualityEncroach_Differ_proposition_4_ii_differentiated
-- name    : QualityEncroach.Differ.proposition_4_ii_differentiated
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-05T04:38:23.381985+00:00
-- url     : https://prove2.me/theorems/792cc212-f239-44b1-aebd-7f47572bd98e
-- title:
--   Proposition 4(ii), case $t^*<1$ — with strict quality differentiation, $\Pi^*_M>1/(54k)$ and $\Pi^*_R<1/(108k)$
-- statement:
--   Consider the encroachment game with quality differentiation of §5. The manufacturer chooses a wholesale price $w$, a quality $u>0$ for the product she sells directly and a quality $tu$, $t>0$, for the product sold through the retailer; the retailer then orders $q_R\ge0$; finally the manufacturer sells $q_M\ge0$ directly. Consumer types are uniform on $[0,1]$, a unit of quality $v$ costs $kv^2$ to produce ($k>0$), and each directly sold unit costs a further $c\ge0$.
--
--   Let $\sigma$ be a subgame-perfect equilibrium in which the manufacturer encroaches, $q^*_M>0$ on the equilibrium path, **and differentiates strictly**, i.e. the retailer carries the strictly lower quality: $t^*<1$. Then the equilibrium profits satisfy
--
--   $$
--   \Pi^*_M>\Pi^N_M=\frac{1}{54k}
--   \qquad\text{and}\qquad
--   \Pi^*_R<\Pi^N_R=\frac{1}{108k},
--   $$
--
--   where $\Pi^N_M$, $\Pi^N_R$ are the benchmark profits without a direct channel (§3.2).
--
--   This is the quality-differentiated branch of Proposition 4(ii) (in Table 1, the region of small direct selling costs, where $t^*=t(u^*)<1$). The complementary branches are covered by other results: Proposition 3 rules out $t^*>1$ under encroachment, and when $t^*=1$ the equilibrium is an equilibrium of the uniform-quality game, so Proposition 1(iii) applies, as the paper's proof of Proposition 4(ii) indicates.
--
--   **Formalization Note.** The case is singled out by the equilibrium ratio $t^*<1$ rather than by the cost threshold $c<c_1$ of Proposition 4(i), so that the statement needs no threshold and matches the case split of the proof. The benchmark profits appear as the constants $\frac1{54k}$ and $\frac1{108k}$, as in Proposition 4(ii).
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 16, Proposition 4(ii) (proof: p. 32), branch t* < 1 (Table 1, c < c1); benchmark profits p. 9

import Mathlib
import Definitions.Def_QualityEncroach_Differ_Game

namespace QualityEncroach.Differ

theorem proposition_4_ii_differentiated (k c : ℝ) (hk : 0 < k) (hc : 0 ≤ c) (σ : Profile)
    (hσ : IsSPE k c (Set.Ioi 0) σ) (henc : 0 < σ.path.qM) (ht : σ.t < 1) :
    1 / (54 * k) < mfrPayoff k c σ.path ∧ retailerPayoff σ.path < 1 / (108 * k) := by sorry

end QualityEncroach.Differ
