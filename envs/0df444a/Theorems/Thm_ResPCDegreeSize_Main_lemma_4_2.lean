-- Prove2me | Theorems.Thm_ResPCDegreeSize_Main_lemma_4_2
-- name    : ResPCDegreeSize.Main.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:26:07.169396+00:00
-- url     : https://prove2.me/theorems/251549fa-da95-431e-b869-71ccf2abf2d5
-- title:
--   Lemma 4.2 — approximation gain
-- statement:
--   Let $Q\supseteq\mathrm{Bool}$, let $g_1,\dots,g_s$ have degree at most $d$, and suppose $P\in V_a$, $K\ge d$ and $a+K+pd\le D$. Then there exists $q\in\mathrm{span}_{\mathbb F_p}\{g_1,\dots,g_s\}$ with
--   $$c_{P(1-q^{p-1})}(K)\le c_P(K)-\Bigl(1-\frac1p\Bigr)c_P(K-d).\tag{29}$$
--
--   One additional Razborov–Smolensky factor therefore removes a definite part of the error rank.
--
--   Differences from the source:
--   - encoding: C_D(Q) is the set of polynomials with a degree-D derivation, "a linear subspace" → an inductive predicate PCDerivable with an extra clause making 0 derivable; CD is its carrier as a submodule of F_p[x]; reason: the source calls C_D a linear subspace, so 0 belongs to it; the clause only matters when no axiom has degree at most D, and derivation trees flatten to the source's sequences
--   - encoding: classes in V_D/C_D → classes in the quotient of the whole ring F_p[x] by C_D; reason: C_D ⊆ V_D, so V_D/C_D embeds in that quotient and every kernel and rank is unchanged; the degree bounds of the statement keep every product inside V_D
--   - encoding: inequality (29) between ranks with a real coefficient → the same inequality with the natural-number ranks cast to ℝ; reason: no truncated subtraction occurs
--   - encoding: F_p[x_1,…,x_n] → MvPolynomial (Fin n) (ZMod p) with [Fact p.Prime]; reason: relabelling of the variables; ZMod p is the field with p elements
-- source:
--   Pang, A Degree–Size Relation for Resolution over Polynomials, 2026 preprint (STOC 2027 submission #128; SHA-256 d026926040f9df67b9f5a3212fe878d8a10b50dd70b04f14b63b62a9dcb9d32f), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/128.pdf, Lemma 4.2, eq. (29), PDF p. 8 (printed p. 7)

import Mathlib
import Definitions.Def_ResPCDegreeSize_Main_PolynomialCalculus
import Definitions.Def_ResPCDegreeSize_Main_RankMaps
open MvPolynomial

namespace ResPCDegreeSize.Main

theorem lemma_4_2 {n p s d a D K : ℕ} [Fact p.Prime]
    (Q : Set (Poly n p)) (hQ : boolAxioms n p ⊆ Q)
    (g : Fin s → Poly n p) (hg : ∀ i, (g i).totalDegree ≤ d)
    (P : Poly n p) (hP : P.totalDegree ≤ a) (hK : d ≤ K) (hD : a + K + p * d ≤ D) :
    ∃ q ∈ Submodule.span (ZMod p) (Set.range g),
      (cRank Q D g (P * (1 - q ^ (p - 1))) K : ℝ) ≤
        (cRank Q D g P K : ℝ) - (1 - 1 / (p : ℝ)) * (cRank Q D g P (K - d) : ℝ) := by sorry

end ResPCDegreeSize.Main
