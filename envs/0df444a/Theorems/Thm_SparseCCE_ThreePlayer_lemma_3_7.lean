-- Prove2me | Theorems.Thm_SparseCCE_ThreePlayer_lemma_3_7
-- name    : SparseCCE.ThreePlayer.lemma_3_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T05:08:50.794696+00:00
-- url     : https://prove2.me/theorems/f6dd6e27-95a1-4654-9dc2-0dbab7038055
-- title:
--   Lemma 3.7 — profitable one-round deviations in the kibitzer game, or an every-type-$\varepsilon_0$ BNE, in polynomial time
-- statement:
--   Fix a rational $\varepsilon_0\in(0,1)$. There is a polynomial-time algorithm that, given $M$ in unary, the code $|G|$ of a valid rational two-player two-action Bayesian game, the horizon $H$, and a listing of a rational legal profile $x$ of the kibitzer game, outputs either (flag `true`) the code of an every-type-$\varepsilon_0$ BNE of $G$, or (flag `false`) a listing of pure legal strategies $x^\dagger_j$ for the three players such that, at every history, a round with $j$ using $x^\dagger_j$ and its opponents using $x$ gives $j$ an expected round payoff of at least $\varepsilon_0$ if $j=K$ and at least $0$ otherwise.
--
--   Differences from the source:
--   - generalization: ε0 the constant of Lemma 3.1(a) → every rational ε0 ∈ (0, 1); reason: the statement and its proof use only the threshold ε0; the source’s constant is one such value
--   - encoding: time polynomial in M and in the encoding lengths of G and x → CookPvsNP.PolyTimeComputable on the input unary(M) ++ |G| ++ H ++ a listing of x (IsLemma37Input); outputs true :: code of y, or false :: a listing of x† (IsDeviationOutput); reason: M in unary turns time polynomial in M into polynomial time in the input length
--   - encoding: the type sets of G (nonempty because the marginals are positive) → instance arguments NeZero (G.n 0), NeZero (G.n 1); reason: implied by validity; needed only to make the kibitzer signal map total
--   - generalization: the kibitzer game with a positive horizon → H may also be zero; reason: At H = 0 the pure-strategy listing is empty and the deviation condition is vacuous in Lemma 3.7; in Lemma 3.8 there are no tests, so the conclusion is 0 ≤ 1/4. Positive horizons specialize to the source
-- source:
--   Fan Chen, Constantinos Daskalakis, Gabriele Farina, Noah Golowich and Charalampos Platanos, "On the Computation of Sparse Equilibria in Normal-Form Games", STOC 2027 submission (citation_basis: published; PDF SHA256 796c83067187974f1685ea4343c0c56d9f89e99484824615342fb7178ee023b5; PDF page = printed page). Lemma 3.7, p. 18; proof App. A.4, p. 31.

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_SparseCCE_ThreePlayer_NormalForm
import Definitions.Def_SparseCCE_ThreePlayer_BayesGame
import Definitions.Def_SparseCCE_ThreePlayer_Kibitzer

namespace SparseCCE.ThreePlayer

/-- **Lemma 3.7 (Profitable one-round deviations)**, p. 18: given a rational legal profile `x` of
the kibitzer game, one can compute, in time polynomial in `M` and in the encoding lengths of `G`
and `x`, either an every-type-`ε₀` BNE of `G`, or pure legal strategies `x†_j` for the three
players such that, at every history, a round with `j` using `x†_j` and its opponents using `x`
gives `j` an expected round payoff of at least `ε₀` if `j = K`, and at least `0` otherwise. -/
theorem lemma_3_7 (ε₀ : ℚ) (hε₀ : 0 < ε₀ ∧ ε₀ < 1) :
    ∃ alg : List Bool → List Bool, CookPvsNP.PolyTimeComputable alg ∧
      ∀ (G : RatBayesGame) [NeZero (G.n 0)] [NeZero (G.n 1)], G.toReal.Valid →
      ∀ (H : ℕ) (x : (j : Fin 3) → (h : Fin H) → (Fin h.val → (kProtocol G.toReal).Outcome) →
          (kProtocol G.toReal).Θ j → (kProtocol G.toReal).A j → ℚ),
        (∀ j h σ θ, IsDist (fun a => (x j h σ θ a : ℝ))) →
        ∀ s, IsLemma37Input G H x s →
          (∃ y : G.RatProfile, alg s = true :: G.profileCode y ∧
              G.toReal.IsEveryTypeBNE (G.profileToReal y) (ε₀ : ℝ)) ∨
          (∃ xd : (j : Fin 3) → (kGame G.toReal H).PureStrategy j,
              IsDeviationOutput G H xd (alg s) ∧
              IsProfitableDeviation G.toReal (ε₀ : ℝ)
                (fun j h σ θ a => (x j h σ θ a : ℝ)) xd) := by sorry

end SparseCCE.ThreePlayer
