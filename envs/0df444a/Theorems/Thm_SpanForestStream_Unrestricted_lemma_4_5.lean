-- Prove2me | Theorems.Thm_SpanForestStream_Unrestricted_lemma_4_5
-- name    : SpanForestStream.Unrestricted.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:32:47.104758+00:00
-- url     : https://prove2.me/theorems/4ebefbec-f5f6-4d3f-aadc-3f2b3cf57b44
-- title:
--   Lemma 4.5 — coordinate reduction with external information (4.18)
-- statement:
--   Let $k$ be even and let $(X_j,Y_j)_{j=1}^k$ be independent pairs with common law $D$. Consider a one-way protocol with randomized message $M$ and possibly randomized output $O=(O_1,\dots,O_k)$ satisfying the Markov conditions $M\leftrightarrow X^k\leftrightarrow Y^k$ and $O\leftrightarrow(M,Y^k)\leftrightarrow X^k$; any shared random seed of the decoder is part of $M$. Let $\pi$ be the joint law of $(X^k,Y^k,M,O)$, suppose it solves all $k$ relations with probability at least $1/2$, and put $J=I_\pi(X^k;M)$. Then there are one input law $D'$ of a pair $(X,Y)$ and one generalized one-coordinate protocol with message $\hat M$ (drawn from $(X,Y)$) and output $O$ (drawn from $(\hat M,Y)$) such that simultaneously
--   $$\begin{aligned}&D_{\mathrm{KL}}(D'[X]\,\|\,D[X]),\ D_{\mathrm{KL}}(D'[Y]\,\|\,D[Y])\le K,\\ &\mathbb E_xD_{\mathrm{KL}}(D'[Y\mid x]\,\|\,D[Y\mid x]),\ \mathbb E_yD_{\mathrm{KL}}(D'[X\mid y]\,\|\,D[X\mid y])\le K/k,\\ &I_{D'}(\hat M;Y\mid X)\le K/k,\quad \Pr_{D'}(\text{error})\le K/\sqrt k,\quad I_{D'}(X;\hat M\mid Y)\le K(J+1)/k,\end{aligned}\qquad(4.18)$$
--   where $K$ is an absolute constant and the conditional expectations use the displayed $D'$ marginals.
--
--   This reduces a $k$-fold one-way problem to a single perturbed coordinate while charging the message's information under its original law.
--
--   Differences from the source:
--   - encoding: k even → k even and 0 < k; reason: at k = 0 the bounds K/k and K/√k are undefined
--   - encoding: the one-way protocol and its Markov conditions → a message kernel from X^k and an output kernel from (M, Y^k) with fresh coins, so the joint law satisfies both Markov conditions by construction; reason: the kernels are exactly the protocols the conditions describe
--   - encoding: the k relations → one relation Rel(x, y, o) applied to each coordinate (X_j, Y_j, O_j); reason: the pairs share the law D and the one-coordinate protocol solves the same relation
--   - encoding: the generalized one-coordinate protocol with message M̂ → a message kernel (x, y) ↦ law of M̂ with values in the original message type, and an output kernel (m, y) ↦ law of O; reason: the construction resamples the original message, so M̂ takes values in M's type
--   - encoding: the absolute constant K and the bounds → ∃ K > 0 before all types and data; bounds in [0,∞] via ofReal, with K(J + 1)/k computed in [0,∞]; reason: J may be infinite
-- source:
--   Chao, Cen, Ma, Wang, Space-Optimal Algorithms for Spanning Forests in Dynamic Streams at Every Confidence Level, arXiv:2611.04365 (PDF sha256 00f5bb17…69c92), p. 30 (PDF 33), Lemma 4.5

import Mathlib
import Definitions.Def_SpanForestStream_Unrestricted_Info
import Definitions.Def_SpanForestStream_Unrestricted_Protocols

open scoped ENNReal

namespace SpanForestStream.Unrestricted

/-- Lemma 4.5 (coordinate reduction with external information): there is an absolute `K > 0`
such that for every even `k`, every law `D` of a pair `(X, Y)`, every relation `Rel` and every
`k`-fold one-way protocol (message from `X^k`, output from `(M, Y^k)`) solving all `k` relations
with probability at least `1/2`, there are an input law `D'` and a generalized one-coordinate
protocol `(M̂, O)` satisfying the seven bounds (4.18), with `J = I_π(X^k; M)`. -/
theorem lemma_4_5 :
    ∃ K : ℝ, 0 < K ∧
      ∀ {X Y Msg Out : Type} (k : ℕ), 0 < k → Even k →
      ∀ (D : PMF (X × Y)) (Rel : X → Y → Out → Prop)
        (msg : (Fin k → X) → PMF Msg) (out : Msg → (Fin k → Y) → PMF (Fin k → Out)),
        (1 / 2 : ℝ≥0∞) ≤ probOf (oneWayJoint D msg out)
            {ω | ∀ j, Rel (ω.1 j).1 (ω.1 j).2 (ω.2.2 j)} →
        ∃ (D' : PMF (X × Y)) (msg' : X → Y → PMF Msg) (out' : Msg → Y → PMF Out),
          klBits (D'.map Prod.fst) (D.map Prod.fst) ≤ ENNReal.ofReal K ∧
          klBits (D'.map Prod.snd) (D.map Prod.snd) ≤ ENNReal.ofReal K ∧
          avgCondKL D' D Prod.fst Prod.snd ≤ ENNReal.ofReal (K / k) ∧
          avgCondKL D' D Prod.snd Prod.fst ≤ ENNReal.ofReal (K / k) ∧
          condMutualInfo (genJoint D' msg' out') (fun ω => ω.2.1) (fun ω => ω.1.2)
              (fun ω => ω.1.1) ≤ ENNReal.ofReal (K / k) ∧
          probOf (genJoint D' msg' out') {ω | ¬ Rel ω.1.1 ω.1.2 ω.2.2} ≤
              ENNReal.ofReal (K / Real.sqrt k) ∧
          condMutualInfo (genJoint D' msg' out') (fun ω => ω.1.1) (fun ω => ω.2.1)
              (fun ω => ω.1.2) ≤
            ENNReal.ofReal K *
              (mutualInfo (oneWayJoint D msg out) (fun ω => fun j => (ω.1 j).1)
                (fun ω => ω.2.1) + 1) / (k : ℝ≥0∞) := by sorry

end SpanForestStream.Unrestricted
