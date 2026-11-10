-- Prove2me | Theorems.Thm_SparseCCE_ThreePlayer_proposition_3_9
-- name    : SparseCCE.ThreePlayer.proposition_3_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:09:46.401915+00:00
-- url     : https://prove2.me/theorems/fdbd9580-0503-4a33-910a-2b178c093ba9
-- title:
--   Proposition 3.9 — a $T$-sparse $\varepsilon$-CCE of the audited kibitzer game yields an every-type-$\varepsilon_0$ BNE, in polynomial time
-- statement:
--   Fix a rational $\varepsilon_0\in(0,1)$. Let $G$ be valid, $H\ge1$, and $T$ satisfy (6): $\sqrt{2\log(36T)/H}\le\varepsilon_0/16$. Let $\mu$ be a $T$-sparse $\varepsilon$-CCE of the audited kibitzer game ($\varepsilon=\lambda\varepsilon_0/64$). Then for every partner choice and every reference profile $x$ of $\mu$, no pure legal strategies $x^\dagger$ satisfy the second alternative of Lemma 3.7 — so Lemma 3.7 applied to $x$ returns an every-type-$\varepsilon_0$ BNE of $G$.
--
--   In particular, for each of the mixture and probability-table input formats there is a polynomial-time algorithm that, given $M$ in unary, $|G|$, $H$, and a $T$-sparse $\varepsilon$-CCE $\mu$ by its rational weights and components (listings of actions with probabilities) or by its rational probability table, outputs the code of an every-type-$\varepsilon_0$ BNE of $G$.
--
--   Differences from the source:
--   - generalization: ε0 the constant of Lemma 3.1(a) → every rational ε0 ∈ (0, 1); reason: the proof uses only the threshold ε0 and (6); the source’s constant is one such value
--   - generalization: Lemma 3.7, applied to the reference profile of µ, returns an every-type-ε0 BNE of G → no pure legal x† satisfies the second alternative of Lemma 3.7 for the reference profile; reason: The contradiction on pp. 18–19 rules out any such strategies; hence every algorithm satisfying Lemma 3.7 must return its first alternative
--   - generalization: the reference profile with the cyclic partners k_i of p. 30 and the source’s choices → every partner choice (both cyclic orders) and every reference profile (every admissible choice at probability-zero pairs and of Lemma 3.2’s laws); reason: covers the source’s profile
--   - encoding: (6) with H the horizon (H ≥ 1; (6) is undefined at H = 0) → an explicit hypothesis 1 ≤ H; reason: Lean’s x/0 = 0 would make (6) hold at H = 0
--   - encoding: time polynomial in M, |G| and the encoding length of µ → CookPvsNP.PolyTimeComputable on unary(M) ++ |G| ++ H ++ T ++ weights ++ listings of the components (IsProp39Input); reason: M in unary turns time polynomial in M into polynomial time in the input length
--   - encoding: the type sets of G (nonempty because the marginals are positive) → instance arguments NeZero (G.n 0), NeZero (G.n 1); reason: implied by validity; needed only to make the kibitzer signal map total
--   - encoding: the decoder uses one- and two-player marginals, obtained from weights/components or a probability table (p. 19) → both IsProp39Input and IsProp39TableInput have uniform polynomial-time decoders; the table has only a real T-sparsity promise; reason: This retains the full source claim for both representations and does not require recovering a factorization
-- source:
--   Fan Chen, Constantinos Daskalakis, Gabriele Farina, Noah Golowich and Charalampos Platanos, "On the Computation of Sparse Equilibria in Normal-Form Games", STOC 2027 submission (citation_basis: published; PDF SHA256 796c83067187974f1685ea4343c0c56d9f89e99484824615342fb7178ee023b5; PDF page = printed page). Proposition 3.9, p. 18; proof pp. 18–19.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SparseCCE_ThreePlayer_NormalForm
import Definitions.Def_SparseCCE_ThreePlayer_BayesGame
import Definitions.Def_SparseCCE_ThreePlayer_ReferenceProfile
import Definitions.Def_SparseCCE_ThreePlayer_Kibitzer
import Definitions.Def_SparseCCE_ThreePlayer_AuditedGame

namespace SparseCCE.ThreePlayer

/-- **Proposition 3.9**, p. 18: let `μ` be a `T`-sparse `ε`-CCE of the normal-form encoding of the
kibitzer game with audits, where `T` satisfies (6), `√(2 log(36T)/H) ≤ ε₀/16`. Then Lemma 3.7,
applied to the reference profile of `μ`, returns an every-type-`ε₀` BNE of `G` (no pure legal
strategies `x†` satisfy its second alternative). In particular, such a BNE can be computed from
`μ` in time polynomial in `M`, `|G|` and the encoding length of `μ`. -/
theorem proposition_3_9 (ε₀ : ℚ) (hε₀ : 0 < ε₀ ∧ ε₀ < 1) :
    (∀ (G : BayesGame) [NeZero (G.n 0)] [NeZero (G.n 1)], G.Valid →
      ∀ H T : ℕ, 1 ≤ H → Real.sqrt (2 * Real.log (36 * (T : ℝ)) / H) ≤ (ε₀ : ℝ) / 16 →
      ∀ μ : ((j : Fin 3) → AAction G H j) → ℝ, IsTSparse T μ →
        IsEpsCCE (auditUtil G H) μ (auditEps G H ε₀) →
        ∀ k : Fin 3 → Fin 3, IsPartnerChoice k →
        ∀ x : (kGame G H).StrategyProfile, (kGame G H).IsReferenceProfile (aTr G H) μ k x →
          ¬ ∃ xd : (j : Fin 3) → (kGame G H).PureStrategy j,
            IsProfitableDeviation G (ε₀ : ℝ) x xd) ∧
    (∃ alg : List Bool → List Bool, CookPvsNP.PolyTimeComputable alg ∧
      ∀ (G : RatBayesGame) [NeZero (G.n 0)] [NeZero (G.n 1)], G.toReal.Valid →
      ∀ H T : ℕ, 1 ≤ H → Real.sqrt (2 * Real.log (36 * (T : ℝ)) / H) ≤ (ε₀ : ℝ) / 16 →
      ∀ (w : Fin T → ℚ) (p : Fin T → (j : Fin 3) → AAction G.toReal H j → ℚ),
        IsDist (fun t => (w t : ℝ)) → (∀ t j, IsDist (fun b => (p t j b : ℝ))) →
        IsEpsCCE (auditUtil G.toReal H)
          (mixture (fun t => (w t : ℝ)) (fun t j b => (p t j b : ℝ))) (auditEps G.toReal H ε₀) →
        ∀ s, IsProp39Input G H T w p s →
          ∃ y : G.RatProfile, alg s = G.profileCode y ∧
            G.toReal.IsEveryTypeBNE (G.profileToReal y) (ε₀ : ℝ)) ∧
    ∃ alg : List Bool → List Bool, CookPvsNP.PolyTimeComputable alg ∧
      ∀ (G : RatBayesGame) [NeZero (G.n 0)] [NeZero (G.n 1)], G.toReal.Valid →
      ∀ H T : ℕ, 1 ≤ H → Real.sqrt (2 * Real.log (36 * (T : ℝ)) / H) ≤ (ε₀ : ℝ) / 16 →
      ∀ μ : ((j : Fin 3) → AAction G.toReal H j) → ℚ,
        IsTSparse T (fun b => (μ b : ℝ)) →
        IsEpsCCE (auditUtil G.toReal H) (fun b => (μ b : ℝ)) (auditEps G.toReal H ε₀) →
        ∀ s, IsProp39TableInput G H T μ s →
          ∃ y : G.RatProfile, alg s = G.profileCode y ∧
            G.toReal.IsEveryTypeBNE (G.profileToReal y) (ε₀ : ℝ) := by sorry

end SparseCCE.ThreePlayer
