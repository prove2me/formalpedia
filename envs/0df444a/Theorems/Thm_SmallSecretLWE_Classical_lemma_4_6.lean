-- Prove2me | Theorems.Thm_SmallSecretLWE_Classical_lemma_4_6
-- name    : SmallSecretLWE.Classical.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:28:10.870219+00:00
-- url     : https://prove2.me/theorems/1ea0cafa-23b5-47c8-8d14-1f324b197e2e
-- title:
--   Lemma 4.6 — Algorithm 1 returns two good walks from a common start with $R$-close endpoints, except with probability $\delta$
-- statement:
--   Let $A\in\mathbb Z_q^{m\times n}$ have exactly $k$ nonzero entries per row and $\lceil k/2\rceil\le l\le n$. For every integer $T\ge1$, every $0\le R<q/2$ and every $\delta\in(0,1/2)$, Algorithm 1 returns, except with probability at most $\delta$, a walk
--   $$W=W_i^{\mathrm{rev}}\circ W_j=(u_0,\dots,u_{2T})$$
--   such that $W_i$ and $W_j$ are good length-$T$ walks from a common starting vertex and $\|u_{2T}-u_0\|_1\le R$.
--
--   Differences from the source:
--   - encoding: $q$ a positive integer, $\mathbb Z_q^n$, indices $1,\dots,n$ → `[NeZero q]`, `Fin n → ZMod q`, indices `0, …, n−1`; reason: Lean convention; same instances
--   - reading: Construction 3.13: edges $u \xrightarrow{a} v$, $v \xrightarrow{-a} u$ for each row $a$ and $v-u=a$ → edge occurrences $(i,\sigma,u)$ (row, sign, tail) with head $u+\sigma a_i\in(\mathbb Z_q^n)_l$; parallel edges kept; reason: with repeated rows or $q=2$ a set of pairs would merge edges that the count $\theta^{(n,l,k)}$ of Eq. (7) and $|E| = m\theta$ count separately; for distinct rows and $q\ne 2$ the two readings coincide
--   - encoding: 'Algorithm 1 returns, except with probability …, a walk …' → `alg1ReturnProb A l T R δ Q`: the probability that Algorithm 1 returns $W_i^{\mathrm{rev}}\circ W_j$ for an iteration outcome $(w_0,W_i,W_j)$ in $Q$; reason: the output law of the procedure, written as a closed form over its independent iterations
--   - encoding: $W_i^{\mathrm{rev}}$ → `joinWalk W_i W_j`: the reverse edge occurrences of $W_i$ in reverse order, then $W_j$, started at the terminal vertex of $W_i$; reason: the reverse of $(i,\sigma,u)$ is $(i,-\sigma,u+\sigma a_i)$, the reverse edge of Observation 4.11
-- source:
--   Agrawal, Bagchi, Kumar, Algorithms for Sparse LWE and LPN with Small Secrets, STOC 2027 submission (manuscript sha256 8d93a268…), p. 21, Lemma 4.6 (Algorithm 1, p. 18)

import Mathlib
import Definitions.Def_SmallSecretLWE_Classical_Kikuchi

namespace SmallSecretLWE.Classical

/-- Lemma 4.6. Let `A ∈ Z_q^{m×n}` have exactly `k` nonzero entries per row and
`⌈k/2⌉ ≤ l ≤ n`. For every integer `T ≥ 1`, `0 ≤ R < q/2` and `δ ∈ (0, 1/2)`, Algorithm 1
returns, except with probability at most `δ`, a walk `W = W_i^rev ∘ W_j = (u_0, …, u_{2T})` such
that `W_i`, `W_j` are good length-`T` walks from a common starting vertex and
`‖u_{2T} − u_0‖_1 ≤ R`. -/
theorem lemma_4_6 {m n q : ℕ} [NeZero q] (k l : ℕ) (A : Matrix (Fin m) (Fin n) (ZMod q))
    (hA : HasKSparseRows k A) (hl₁ : (k + 1) / 2 ≤ l) (hl₂ : l ≤ n) (T : ℕ) (hT : 1 ≤ T)
    (R : ℝ) (hR₀ : 0 ≤ R) (hRq : R < (q : ℝ) / 2) (δ : ℝ) (hδ₀ : 0 < δ) (hδ : δ < 1 / 2) :
    1 - δ ≤ alg1ReturnProb A l T R δ (fun x =>
      let G := kikuchi A l
      let u₀ := G.walkVtx x.1 x.2.1 (Fin.last T)
      G.IsWalk x.1 x.2.1 ∧ G.IsWalk x.1 x.2.2 ∧ G.IsGood x.1 x.2.1 ∧ G.IsGood x.1 x.2.2 ∧
        G.IsWalk u₀ (joinWalk x.2.1 x.2.2) ∧
        l1 ((G.walkVtx u₀ (joinWalk x.2.1 x.2.2) (Fin.last (T + T))).val - u₀.val) ≤ R) := by sorry

end SmallSecretLWE.Classical
