-- Prove2me | Theorems.Thm_SecondBestMatch_Supplement_theorem_5_2
-- name    : SecondBestMatch.Supplement.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:43:56.95554+00:00
-- url     : https://prove2.me/theorems/e0340286-bfd2-44a1-b1fd-e86defbe301d
-- title:
--   Theorem 5.2 — the subsidy–efficiency frontier is $\gamma(\delta)=\inf_{\alpha\ge0}(g_\alpha+\alpha\delta)$, approached by bilateral finite-support instances
-- statement:
--   **Efficiency with a subsidy.** Consider matching-market instances $\mathcal I$: finitely many buyers $B$ and sellers $S$, edges $E$, a nonempty downward-closed family $\mathcal F$ of matchings, and independent Borel priors on $[0,1]$. For $s\ge0$ let
--
--   $$
--   \mathrm{SB}_s(\mathcal I):=\sup\{\mathrm{GFT}(q):(q,p,r)\text{ is BIC, interim IR, and has expected deficit at most } s\},
--   $$
--
--   and for $\delta\ge0$ let $\gamma(\delta):=\inf_{\mathcal I:\,\mathrm{FB}(\mathcal I)>0}\mathrm{SB}_{\delta\,\mathrm{FB}(\mathcal I)}(\mathcal I)/\mathrm{FB}(\mathcal I)$ (Definition 5.1). Then for every $\delta\ge0$
--
--   $$
--   \gamma(\delta)=\Gamma(\delta):=\inf_{\alpha\ge0}\big(g_\alpha+\alpha\delta\big),\qquad g_\alpha=\frac{1+\alpha}{\mathrm B\!\left(\frac1{1+\alpha},\frac1{1+\alpha}\right)},\qquad(8)
--   $$
--
--   and the infimum defining $\gamma(\delta)$ is approached by bilateral instances with finite-support priors. Concretely:
--
--   1. **(lower bound)** for every instance with $\mathrm{FB}>0$ and every $\varepsilon>0$ there is a BIC, interim-IR mechanism with expected deficit at most $\delta\,\mathrm{FB}$ whose gains from trade are at least $(\Gamma(\delta)-\varepsilon)\,\mathrm{FB}$;
--   2. **(tightness)** for every $\varepsilon>0$ there is a bilateral instance (one buyer, one seller, one edge, $\mathcal F=\{\emptyset,\{e\}\}$) with finite-support priors on $[0,1]$ and $\mathrm{FB}>0$ on which every BIC, interim-IR mechanism with expected deficit at most $\delta\,\mathrm{FB}$ has gains from trade at most $(\Gamma(\delta)+\varepsilon)\,\mathrm{FB}$.
--
--   At $\alpha=0$ the formula gives $g_0=1$, and at $\delta=0$ the theorem recovers $\gamma(0)=1/2$. The frontier $\gamma$ measures the best efficiency guarantee when an outside party contributes a $\delta$ fraction of the first-best gains from trade.
--
--   **Formalization Note** $\gamma$ and $\mathrm{SB}_s$ are not defined as real infima and suprema. The two clauses state the identity through witnesses and bounds, so no junk value can enter. $\Gamma(\delta)$ is a real `sInf` over $\{g_\alpha+\alpha\delta:\alpha\ge0\}$, a nonempty set bounded below by $0$, hence the genuine infimum. Mechanisms carry the mission's standing assumption `IsAdmissible`: a Borel kernel into $\Delta(\mathcal F)$ with finite transfer expectations (p.8). BIC and interim IR are on the full report domain $[0,1]$. No budget condition other than the expected deficit is imposed.
--
--   Differences from the source:
--   - encoding: γ(δ) := inf over instances with FB > 0 of SB_{δFB}/FB, with SB_s a supremum (Definition 5.1) → clause (a): every instance with FB > 0 has, for every ε > 0, a feasible mechanism with GFT ≥ (Γ(δ) − ε)·FB; clause (b): for every ε > 0 a bilateral finite-support instance on which every feasible mechanism has GFT ≤ (Γ(δ) + ε)·FB; reason: (a) is SB_{δFB} ≥ Γ(δ)·FB for every instance, i.e. γ(δ) ≥ Γ(δ), and (b) is γ(δ) ≤ Γ(δ) witnessed by bilateral finite-support instances; together exactly the theorem, with no real sSup/sInf over possibly empty or unbounded sets
--   - encoding: instances of Section 2 → Market B S with B, S finite types in Type, IsUnitMarket; bilateral instances on Market (Fin 1) (Fin 1) with edges {(0,0)} and family {∅, {(0,0)}}; reason: the mission's published model; a bilateral instance with FB > 0 must have its one edge
--   - encoding: mechanisms (q, p, r) in SB_s (Borel kernel, finite transfer expectations, BIC and interim IR) → IsAdmissible ∧ IsBIC ∧ IsInterimIR, with BIC and IR on the full report domain [0,1]; reason: the paper's standing assumptions of p.8, encoded exactly as in the published secondBest; no instance changes
-- source:
--   Bei–Li–Wu–Zhou, Second-Best Gains from Trade in Matching Markets, arXiv:2609.18724 (held version, sha256 ea1808ea7cce1bbfc7757c56937ec4ac13847b6d0025758a63fa8d6a25314385), Theorem 5.2 and Definition 5.1, p.22 (eq. (8))

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_SecondBestMatch_IsUnitMarket
import Definitions.Def_SecondBestMatch_IsFiniteSupportMarket
import Definitions.Def_SecondBestMatch_IsAdmissible
import Definitions.Def_SecondBestMatch_IsBIC
import Definitions.Def_SecondBestMatch_IsInterimIR
import Definitions.Def_SecondBestMatch_ordGFT
import Definitions.Def_SecondBestMatch_firstBestGFT
import Definitions.Def_SecondBestMatch_gCoeff
import Definitions.Def_SecondBestMatch_Supplement_HasDeficitAtMost

open MeasureTheory Set MatchingGFT.TightE

namespace SecondBestMatch.Supplement

/-- **Theorem 5.2** (Efficiency with a subsidy; Bei–Li–Wu–Zhou, *Second-Best Gains from Trade in Matching Markets*, arXiv:2609.18724 (held version, sha256 ea1808ea…14385), §5.1, p.22). For every `δ ≥ 0`,
`γ(δ) = inf_{α ≥ 0} (g_α + α δ)` with `g_α = (1 + α)/B(1/(1+α), 1/(1+α))` (8), where
`γ(δ) := inf_{ℐ : FB(ℐ) > 0} SB_{δ FB(ℐ)}(ℐ) / FB(ℐ)` over all instances of Section 2 and
`SB_s(ℐ) := sup {GFT(q) : (q, p, r) is BIC, interim IR, and has expected deficit at most s}`
(Definition 5.1). Moreover, the infimum defining `γ(δ)` is approached by bilateral instances with
finite-support priors.

Writing `Γ(δ) := inf_{α ≥ 0} (g_α + α δ)`, the statement is the conjunction of
(a) every instance with `FB > 0` has `SB_{δ FB} ≥ Γ(δ) FB`: for every `ε > 0` some admissible,
BIC, interim-IR mechanism with expected deficit at most `δ FB` has `GFT ≥ (Γ(δ) − ε) FB`; and
(b) for every `ε > 0` a bilateral instance (one buyer, one seller, one edge, `ℱ = {∅, {e}}`) with
finite-support priors on `[0, 1]` and `FB > 0` on which every such mechanism has
`GFT ≤ (Γ(δ) + ε) FB`.
Together, (a) and (b) say exactly that `γ(δ) = Γ(δ)` and that the infimum is approached by
bilateral finite-support instances.

**Formalization Note** `γ` and `SB_s` are not defined as real `sInf`/`sSup`; the two clauses
state the identity through witnesses and bounds, so no junk value can enter. `Γ(δ)` is a real
`sInf` of `{g_α + α δ : α ≥ 0}`, which is nonempty and bounded below by `0` (`g_α > 0`), hence a
genuine infimum; `α = 0` is included. `g_α` is the published `gCoeff`. Mechanisms carry the
paper's standing assumption `IsAdmissible` (Borel kernel into `Δ(ℱ)`, finite transfer
expectations, p.8); no budget condition other than the expected deficit is imposed. -/
theorem theorem_5_2 (δ : ℝ) (hδ : 0 ≤ δ) :
    (∀ {B S : Type} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S] (m : Market B S),
      IsUnitMarket m → 0 < firstBestGFT m → ∀ ε : ℝ, 0 < ε →
        ∃ A : Mechanism B S, IsAdmissible m A ∧ IsBIC m A ∧ IsInterimIR m A ∧
          HasDeficitAtMost m A (δ * firstBestGFT m) ∧
          (sInf ((fun α : ℝ => gCoeff α + α * δ) '' Ici 0) - ε) * firstBestGFT m ≤
            ordGFT m A.alloc) ∧
    (∀ ε : ℝ, 0 < ε → ∃ m : Market (Fin 1) (Fin 1),
      m.edges = {(0, 0)} ∧ m.family = {∅, {(0, 0)}} ∧ IsUnitMarket m ∧
        IsFiniteSupportMarket m ∧ 0 < firstBestGFT m ∧
        ∀ A : Mechanism (Fin 1) (Fin 1), IsAdmissible m A → IsBIC m A → IsInterimIR m A →
          HasDeficitAtMost m A (δ * firstBestGFT m) →
          ordGFT m A.alloc ≤
            (sInf ((fun α : ℝ => gCoeff α + α * δ) '' Ici 0) + ε) * firstBestGFT m) := by sorry

end SecondBestMatch.Supplement
