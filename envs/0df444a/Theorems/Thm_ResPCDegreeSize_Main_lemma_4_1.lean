-- Prove2me | Theorems.Thm_ResPCDegreeSize_Main_lemma_4_1
-- name    : ResPCDegreeSize.Main.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:25:41.80921+00:00
-- url     : https://prove2.me/theorems/7dedc987-1a5f-4112-8914-f81033ee80e4
-- title:
--   Lemma 4.1 — normalized rank is nonincreasing
-- statement:
--   Let $Q\supseteq\mathrm{Bool}$, let $g_1,\dots,g_s$ have degree at most $d$, and let $P\in V_a$. Let $a+K+d\le D$ and $K\le n$. Then the normalized rank $c_P(k)/N_n(k)$ is nonincreasing for $0\le k\le K$. In particular, if $K\ge d$, then
--   $$c_P(K-d)\ge\frac{N_n(K-d)}{N_n(K)}\,c_P(K).\tag{28}$$
--
--   Here $c_P(k)$ is the rank of $T_{P,k}:f\mapsto([Pg_if])_i$ on $V_k$, and $N_n(k)=\sum_{j\le k}\binom nj$. The lemma lets a rank at degree $K$ be recovered, up to a counting factor, at the lower degree $K-d$.
--
--   Differences from the source:
--   - encoding: C_D(Q) is the set of polynomials with a degree-D derivation, "a linear subspace" → an inductive predicate PCDerivable with an extra clause making 0 derivable; CD is its carrier as a submodule of F_p[x]; reason: the source calls C_D a linear subspace, so 0 belongs to it; the clause only matters when no axiom has degree at most D, and derivation trees flatten to the source's sequences
--   - encoding: classes in V_D/C_D → classes in the quotient of the whole ring F_p[x] by C_D; reason: C_D ⊆ V_D, so V_D/C_D embeds in that quotient and every kernel and rank is unchanged; the degree bounds of the statement keep every product inside V_D
--   - encoding: F_p[x_1,…,x_n] → MvPolynomial (Fin n) (ZMod p) with [Fact p.Prime]; reason: relabelling of the variables; ZMod p is the field with p elements
-- source:
--   Pang, A Degree–Size Relation for Resolution over Polynomials, 2026 preprint (STOC 2027 submission #128; SHA-256 d026926040f9df67b9f5a3212fe878d8a10b50dd70b04f14b63b62a9dcb9d32f), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/128.pdf, Lemma 4.1, eq. (28), PDF p. 7 (printed p. 6)

import Mathlib
import Definitions.Def_ResPCDegreeSize_Main_PolynomialCalculus
import Definitions.Def_ResPCDegreeSize_Main_RankMaps
open MvPolynomial

namespace ResPCDegreeSize.Main

theorem lemma_4_1 {n p s d a D K : ℕ} [Fact p.Prime]
    (Q : Set (Poly n p)) (hQ : boolAxioms n p ⊆ Q)
    (g : Fin s → Poly n p) (hg : ∀ i, (g i).totalDegree ≤ d)
    (P : Poly n p) (hP : P.totalDegree ≤ a) (hD : a + K + d ≤ D) (hK : K ≤ n) :
    (∀ k k' : ℕ, k ≤ k' → k' ≤ K →
      (cRank Q D g P k' : ℝ) / (Nn n k' : ℝ) ≤ (cRank Q D g P k : ℝ) / (Nn n k : ℝ)) ∧
    (d ≤ K →
      (Nn n (K - d) : ℝ) / (Nn n K : ℝ) * (cRank Q D g P K : ℝ) ≤
        (cRank Q D g P (K - d) : ℝ)) := by sorry

end ResPCDegreeSize.Main
