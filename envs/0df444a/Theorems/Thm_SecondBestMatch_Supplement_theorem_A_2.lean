-- Prove2me | Theorems.Thm_SecondBestMatch_Supplement_theorem_A_2
-- name    : SecondBestMatch.Supplement.theorem_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:44:42.12394+00:00
-- url     : https://prove2.me/theorems/ba55fa3f-6926-417b-b5f9-d6448d040089
-- title:
--   Theorem A.2 — $\mathrm{SB}$ is the attained maximum of the full-potential program, and every maximizer induces a feasible second-best mechanism
-- statement:
--   Let $\mathcal I$ be a matching-market instance with arbitrary mutually independent Borel priors $F_i$, $G_j$ on $[0,1]$. Then
--
--   $$
--   \mathrm{SB}(\mathcal I)=\max\big\{\mathcal G(x,y):(x,y,U)\text{ is full-potential feasible}\big\}.\qquad(17)
--   $$
--
--   Moreover, every maximizer induces a mechanism that is BIC and interim IR on the full report domain and has deterministic transfers satisfying exact strong budget balance at every report profile. Precisely:
--
--   1. **(attainment and value)** some full-potential feasible tuple $(x^*,y^*,U^*)$ maximizes $\mathcal G$ over all full-potential feasible tuples, and $\mathcal G(x^*,y^*)=\mathrm{SB}(\mathcal I)$;
--   2. **(implementation)** for every maximizer $(x,y,U)$ there is a mechanism $(q,p,r)$ with the following properties:
--      - it is admissible, BIC and interim IR on $[0,1]$, and balances its budget exactly at every report profile of $[0,1]^K$;
--      - its gains from trade equal $\mathcal G(x,y)$;
--      - its interim service rules agree with $x_i$ ($F_i$-a.e.) and $y_j$ ($G_j$-a.e.);
--      - its truthful interim utilities equal the potentials at every type: $v\,x_i^q(v)-p_i(v)=U_i(v)$ and $r_j(c)-c\,y_j^q(c)=U_j(c)$ for all $v,c\in[0,1]$.
--
--   Here $\mathrm{SB}(\mathcal I)$ is the supremum of the gains from trade over BIC, interim-IR, exactly strongly budget-balanced mechanisms, and $\mathcal G$ is the reduced-form objective. The theorem makes incentive compatibility on the whole report domain explicit and shows that the second best is attained for arbitrary priors.
--
--   **Formalization Note** "max" is written as attainment plus value, so no real supremum of the program appears; $\mathrm{SB}$ is the mission's published `secondBest`. Transfers are deterministic by the type of `Mechanism`.
--
--   Differences from the source:
--   - reading: every maximizer induces a mechanism that is BIC and interim IR on the full report domain with exact strong budget balance → for every maximizer an IsSBFeasible mechanism with the same GFT, interim service rules equal to (x, y) almost everywhere, and truthful interim utilities equal to the potentials at every type in [0,1]; reason: "induces" is ambiguous; this is what Lemmas A.4–A.5 (pp.28–30) construct ("preserve every interim payment and utility") and it is the stronger reading
--   - encoding: SB(ℐ) = max {𝒢(x, y) : (x, y, U) full-potential feasible} → ∃ a feasible τ with 𝒢 τ ≥ 𝒢 τ' for every feasible τ' and 𝒢 τ = secondBest m; reason: "max" is attainment plus value; no real sSup of the program is taken
--   - encoding: reduced forms in Π L∞(Fᵢ) × Π L∞(Gⱼ) identified a.e., potentials U_k : [0,1] → ℝ≥0, agent set K → functions ℝ → ℝ, membership in ℛ through =ᵐ equalities with the interim service rules of a kernel, potentials constrained (nonnegative, convex, monotone, d_k-Lipschitz) on Icc 0 1 only, K = B ⊕ S; reason: the priors live on [0,1], so values off [0,1] and on null sets never enter; no instance changes
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea7cce1bbfc7757c56937ec4ac13847b6d0025758a63fa8d6a25314385), Theorem A.2, p.28 (eq. (17)); Definition A.1, p.27; Lemmas A.4–A.5, pp.28–30

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_IsUnitMarket
import Definitions.Def_SecondBestMatch_IsSBFeasible
import Definitions.Def_SecondBestMatch_interimBuyerService
import Definitions.Def_SecondBestMatch_interimSellerService
import Definitions.Def_SecondBestMatch_interimPay
import Definitions.Def_SecondBestMatch_interimRecv
import Definitions.Def_SecondBestMatch_ordGFT
import Definitions.Def_SecondBestMatch_secondBest
import Definitions.Def_SecondBestMatch_Supplement_IsFullPotentialFeasible
import Definitions.Def_SecondBestMatch_Supplement_reducedGFT

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch.Supplement

/-- **Theorem A.2** (Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), Appendix A.1, p.28). For arbitrary mutually independent Borel priors on
`[0, 1]`, `SB(ℐ) = max {𝒢(x, y) : (x, y, U) is full-potential feasible}` (17). Every maximizer
induces a mechanism that is BIC and interim IR on the full report domain and has deterministic
transfers satisfying exact strong budget balance at every report profile.

Clause (1): the maximum is attained (some full-potential feasible tuple maximizes `𝒢`) and its
value is `SB(ℐ)`. Clause (2): for every maximizer `τ = (x, y, U)` there is a mechanism
`(q, p, r)` that is admissible, BIC and interim IR on `[0, 1]` and exactly strongly budget
balanced at every profile of `[0, 1]^K` (`IsSBFeasible`), whose GFT is `𝒢(x, y)`, whose interim
service rules agree with `(x, y)` almost everywhere, and whose truthful interim utilities equal the
potentials at every type in `[0, 1]`.

**Formalization Note** "Induces" is read as in Lemmas A.4–A.5 (pp.28–30), which construct the
mechanism: same reduced form almost everywhere, same GFT, interim utilities
`v xᵢ(v) − pᵢ(v) = Uᵢ(v)` and `rⱼ(c) − c yⱼ(c) = Uⱼ(c)` on the whole report domain. Transfers are
deterministic by the type of `Mechanism`. "max" is written as attainment plus value, so no real
`sSup` of the program appears; `SB(ℐ)` is the published `secondBest`. -/
theorem theorem_A_2 {B S : Type} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S]
    (m : Market B S) (hm : IsUnitMarket m) :
    (∃ τ : FullPotentialTuple B S, IsFullPotentialFeasible m τ ∧
      (∀ τ' : FullPotentialTuple B S, IsFullPotentialFeasible m τ' →
        reducedGFT m τ'.x τ'.y ≤ reducedGFT m τ.x τ.y) ∧
      reducedGFT m τ.x τ.y = secondBest m) ∧
    (∀ τ : FullPotentialTuple B S, IsFullPotentialFeasible m τ →
      (∀ τ' : FullPotentialTuple B S, IsFullPotentialFeasible m τ' →
        reducedGFT m τ'.x τ'.y ≤ reducedGFT m τ.x τ.y) →
      ∃ A : Mechanism B S, IsSBFeasible m A ∧ ordGFT m A.alloc = reducedGFT m τ.x τ.y ∧
        (∀ i, interimBuyerService m A.alloc i =ᵐ[m.buyerLaw i] τ.x i) ∧
        (∀ j, interimSellerService m A.alloc j =ᵐ[m.sellerLaw j] τ.y j) ∧
        (∀ i, ∀ v ∈ Icc (0 : ℝ) 1,
          v * interimBuyerService m A.alloc i v - interimPay m A i v = τ.U (Sum.inl i) v) ∧
        (∀ j, ∀ c ∈ Icc (0 : ℝ) 1,
          interimRecv m A j c - c * interimSellerService m A.alloc j c = τ.U (Sum.inr j) c)) := by sorry

end SecondBestMatch.Supplement
