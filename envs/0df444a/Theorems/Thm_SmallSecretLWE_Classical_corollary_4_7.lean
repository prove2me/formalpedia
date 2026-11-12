-- Prove2me | Theorems.Thm_SmallSecretLWE_Classical_corollary_4_7
-- name    : SmallSecretLWE.Classical.corollary_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T05:27:58.80206+00:00
-- url     : https://prove2.me/theorems/d9a59d4f-b0c7-4638-a24c-8c467de5fb5f
-- title:
--   Corollary 4.7 — under (11) Algorithm 1's walk also has $\mathrm{Single}(W)\not\subseteq B$, except with probability $2\delta$
-- statement:
--   Let $A,l,T,R$ satisfy the hypotheses of Lemma 4.6, $N=\binom nl(q-1)^l$, $M=N/\binom{\lfloor R/4\rfloor+l}{l}$, $\alpha\in(0,1)$, $\delta\in(0,1/2)$, $L=\lceil128\sqrt M\rceil$, $J=\lceil16\ln(1/\delta)\rceil$ and $\Delta=|E(K_l(A))|/N$. Fix $B\subseteq[m]$ with $|B|\le2T$ and suppose
--   $$\Delta\ge\frac{700T}{\alpha},\qquad T\ge\frac{2}{\ln(1/\alpha)}\Big(\ln M+\ln\frac1\delta+\ln\ln\frac1\delta+12\Big)\ge\frac{2}{\ln(1/\alpha)}\ln\frac{J\binom L2}{\delta}. \tag{11}$$
--   Then Algorithm 1 returns, except with probability at most $2\delta$, a length-$2T$ walk $W=(u_0,\dots,u_{2T})$ with
--   $$\|u_{2T}-u_0\|_1\le R,\qquad \mathrm{Single}(W)\not\subseteq B .$$
--
--   Differences from the source:
--   - encoding: $q$ a positive integer, $\mathbb Z_q^n$, indices $1,\dots,n$ → `[NeZero q]`, `Fin n → ZMod q`, indices `0, …, n−1`; reason: Lean convention; same instances
--   - reading: Construction 3.13: edges $u \xrightarrow{a} v$, $v \xrightarrow{-a} u$ for each row $a$ and $v-u=a$ → edge occurrences $(i,\sigma,u)$ (row, sign, tail) with head $u+\sigma a_i\in(\mathbb Z_q^n)_l$; parallel edges kept; reason: with repeated rows or $q=2$ a set of pairs would merge edges that the count $\theta^{(n,l,k)}$ of Eq. (7) and $|E| = m\theta$ count separately; for distinct rows and $q\ne 2$ the two readings coincide
--   - encoding: 'Algorithm 1 returns, except with probability …, a walk …' → `alg1ReturnProb A l T R δ Q`: the probability that Algorithm 1 returns $W_i^{\mathrm{rev}}\circ W_j$ for an iteration outcome $(w_0,W_i,W_j)$ in $Q$; reason: the output law of the procedure, written as a closed form over its independent iterations
--   - reading: $\Delta=|E(K_l(A))|/N=m\theta(n,l,k)/N$ → $\Delta=|E(K_l(A))|/N$ with $|E|$ the number of edge occurrences; reason: the first printed expression is the definition; the second is a claimed identity
--   - reading: (11), a chain 'Suppose $\Delta\ge\dots$, $T\ge X\ge Y$' → three hypotheses: $\Delta\ge700T/\alpha$, $X\le T$ and $Y\le X$; reason: everything after 'Suppose' is supposed, as printed
--   - encoding: $\mathrm{Single}(W)$, $W=W_i^{\mathrm{rev}}\circ W_j$ → `single kColor (walkEdges (joinWalk W_i W_j))`; reason: colors of the multiset of edges of $W$
-- source:
--   Agrawal, Bagchi, Kumar, Algorithms for Sparse LWE and LPN with Small Secrets, STOC 2027 submission (manuscript sha256 8d93a268…), p. 22, Corollary 4.7

import Mathlib
import Definitions.Def_SmallSecretLWE_Classical_Kikuchi

namespace SmallSecretLWE.Classical

/-- Corollary 4.7. Under the hypotheses of Lemma 4.6, with `α ∈ (0, 1)`, `δ ∈ (0, 1/2)`,
`L = ⌈128 √M⌉`, `J = ⌈16 ln(1/δ)⌉`, `Δ = |E(K_l(A))|/N`, and a fixed `B ⊆ [m]` with
`|B| ≤ 2T`: if `Δ ≥ 700T/α` and
`T ≥ (2/ln(1/α))(ln M + ln(1/δ) + ln ln(1/δ) + 12) ≥ (2/ln(1/α)) ln(J binom(L,2)/δ)` (11),
then Algorithm 1 returns, except with probability at most `2δ`, a length-`2T` walk
`W = (u_0, …, u_{2T})` with `‖u_{2T} − u_0‖_1 ≤ R` and `Single(W) ⊄ B`. -/
theorem corollary_4_7 {m n q : ℕ} [NeZero q] (k l : ℕ) (A : Matrix (Fin m) (Fin n) (ZMod q))
    (hA : HasKSparseRows k A) (hl₁ : (k + 1) / 2 ≤ l) (hl₂ : l ≤ n) (T : ℕ) (hT : 1 ≤ T)
    (R : ℝ) (hR₀ : 0 ≤ R) (hRq : R < (q : ℝ) / 2) (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1)
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ : δ < 1 / 2) (B : Finset (Fin m)) (hB : B.card ≤ 2 * T)
    (hΔ : 700 * (T : ℝ) / α ≤ (Fintype.card (KEdge A l) : ℝ) / alg1N n l q)
    (hT₁ : 2 / Real.log (1 / α) * (Real.log (alg1M n l q R) + Real.log (1 / δ) +
        Real.log (Real.log (1 / δ)) + 12) ≤ T)
    (hT₂ : 2 / Real.log (1 / α) *
        Real.log ((alg1J δ : ℝ) * ((alg1L n l q R).choose 2 : ℝ) / δ) ≤
      2 / Real.log (1 / α) * (Real.log (alg1M n l q R) + Real.log (1 / δ) +
        Real.log (Real.log (1 / δ)) + 12)) :
    1 - 2 * δ ≤ alg1ReturnProb A l T R δ (fun x =>
      let G := kikuchi A l
      let u₀ := G.walkVtx x.1 x.2.1 (Fin.last T)
      G.IsWalk u₀ (joinWalk x.2.1 x.2.2) ∧
        l1 ((G.walkVtx u₀ (joinWalk x.2.1 x.2.2) (Fin.last (T + T))).val - u₀.val) ≤ R ∧
        ¬ single kColor (walkEdges (joinWalk x.2.1 x.2.2)) ⊆ B) := by sorry

end SmallSecretLWE.Classical
