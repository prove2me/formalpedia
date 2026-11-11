-- Prove2me | Theorems.Thm_RSBeyondJohnson_FirstOrder_lemma_3_14
-- name    : RSBeyondJohnson.FirstOrder.lemma_3_14
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:32:25.504207+00:00
-- url     : https://prove2.me/theorems/c3b87571-7e83-4836-baa1-6fe0ad4cfb75
-- title:
--   Lemma 3.14 — first-order dimension and rank
-- statement:
--   Fix $\delta>0$, integers $m\ge1$, $B_\partial\ge0$, $B_{\mathrm{jet}}\ge1$, $n\ge2$, $1\le k\le n$, $k+\delta n\le A\le n$, and put $K=\max\{k,2\}$, $D=K-1$. Over any field, the first-order support $\mathcal V=\mathcal V_{m,B_\partial,B_{\mathrm{jet}}}$ of (19) is invariant under translations in $X$ and $Y_0$, has total jet degree at most $B_{\mathrm{jet}}$, and specializes to degree less than $mA$ at every polynomial of degree less than $K$. Its order-one, multiplicity-$m$ local constraint map $\Phi^{1,m}_{\alpha,y}$ has rank at most $R_{\mathrm{loc}}(m,B_\partial)$ at every received point $(\alpha,y)$. Its coefficient count satisfies
--   $$N_{\mathrm{coef}}=\dim\mathcal V=\sum_{t=0}^{B_{\mathrm{jet}}}N_{\mathrm{jet}}(t)(mA-Dt)_+\ \ge\ n\sum_{t=0}^{B_{\mathrm{jet}}}N_{\mathrm{jet}}(t)\Big(m\delta+\frac kn(m-t)\Big)_+.$$
--
--   Differences from the source:
--   - encoding: K = max{k, 2}, D = K − 1 → natural parameters K, D with hypotheses K = max k 2 and D = K − 1; reason: the paper's abbreviations
--   - encoding: uniformly over the received point → ∀ α y : F; reason: same
--   - encoding: integer identity for N_coef and the real lower bound → the identity in ℤ with (·)_+ = max 0, the lower bound in ℝ; reason: exact arithmetic of the printed expressions
-- source:
--   Dao, Kominers, Thaler, Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs, STOC 2027 submission (manuscript of November 2, 2026, sha256 76a38731…), p. 21, Lemma 3.14

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Decoding
import Definitions.Def_RSBeyondJohnson_FirstOrder_Interpolation
import Definitions.Def_RSBeyondJohnson_FirstOrder_Params

open Finset

open Polynomial

namespace RSBeyondJohnson.FirstOrder

/-- **Lemma 3.14 (First-order dimension and rank)**, p. 21. Let `δ > 0`, `m ≥ 1`, `B∂ ≥ 0`,
`B_jet ≥ 1`, `n ≥ 2`, `1 ≤ k ≤ n`, `k + δn ≤ A ≤ n`, `K = max{k, 2}`, `D = K − 1`. Over any field
the first-order support `V = V_{m,B∂,B_jet}` (19) is invariant under translations in `X` and
`Y₀`, has total jet degree at most `B_jet`, and specializes to degree `< mA` at every polynomial
of degree `< K`; its order-one, multiplicity-`m` local constraint map has rank at most
`R_loc(m, B∂)` at every received point; and
`N_coef = dim V = ∑_{t=0}^{B_jet} N_jet(t)(mA − Dt)_+ ≥ n ∑_{t=0}^{B_jet} N_jet(t)(mδ + (k/n)(m − t))_+`. -/
theorem lemma_3_14 (F : Type*) [Field F] (δ : ℝ) (hδ : 0 < δ) (m Bd Bjet n k A K D : ℕ)
    (hm : 1 ≤ m) (hBjet : 1 ≤ Bjet) (hn : 2 ≤ n) (hk1 : 1 ≤ k) (hkn : k ≤ n)
    (hA : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) (hK : K = max k 2) (hD : D = K - 1) :
    (∀ a b : F, ∀ Q ∈ firstOrderSupport F m Bd Bjet D A,
      translateXY0 1 a b Q ∈ firstOrderSupport F m Bd Bjet D A) ∧
    (∀ Q ∈ firstOrderSupport F m Bd Bjet D A, jetDegree Q ≤ Bjet) ∧
    (∀ Q ∈ firstOrderSupport F m Bd Bjet D A, ∀ P : F[X], P.degree < (K : WithBot ℕ) →
      (RSListDecodingCapacity.AllRates.hasseJetEval 1 Q P).degree < ((m * A : ℕ) : WithBot ℕ)) ∧
    (∀ α y : F, (Module.finrank F (LinearMap.range
      ((localConstraintMap 1 m α y).domRestrict (firstOrderSupport F m Bd Bjet D A))) : ℤ)
        ≤ rLoc m Bd) ∧
    ((Module.finrank F (firstOrderSupport F m Bd Bjet D A) : ℤ) =
      ∑ t ∈ range (Bjet + 1), (nJet Bd t : ℤ) * max 0 ((m : ℤ) * A - (D : ℤ) * t)) ∧
    ((n : ℝ) * ∑ t ∈ range (Bjet + 1),
        (nJet Bd t : ℝ) * max 0 ((m : ℝ) * δ + ((k : ℝ) / n) * ((m : ℝ) - t)) ≤
      (Module.finrank F (firstOrderSupport F m Bd Bjet D A) : ℝ)) := by sorry

end RSBeyondJohnson.FirstOrder
