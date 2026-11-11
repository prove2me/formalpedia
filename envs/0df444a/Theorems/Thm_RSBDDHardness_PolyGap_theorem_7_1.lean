-- Prove2me | Theorems.Thm_RSBDDHardness_PolyGap_theorem_7_1
-- name    : RSBDDHardness.PolyGap.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:27:12.2029+00:00
-- url     : https://prove2.me/theorems/706d3677-a639-4043-b44f-a2f59e5d9ef9
-- title:
--   Theorem 7.1 — balanced universal completion
-- statement:
--   Throughout, $q$ is prime, $t\ge1$, $P\in\mathbb F_q[Z]$ is monic irreducible of degree $L=2t+1$, $\mathbb K=\mathbb F_q[Z]/(P)$, $\theta=Z\bmod P$ and $H=\operatorname{span}_{\mathbb F_q}\{1,\theta,\dots,\theta^t\}$ (the setting of §6.1).
--
--   Let $B\subseteq H\setminus\{0\}$ be a projectively distinct set of even size satisfying (31) and (32) for the cutoff $d$, and let $D=\bigcup_{\beta\in B}\beta\mathbb F_q^\times$. Let $1\le d<q-1$. Suppose that for a fixed integer $1\le h<q$ every vector of $\mathbb F_q^d$ is the vector of the first $d$ moments of an $h$-element subset of $\mathbb F_q^\times$. Then for every residual vector $r_1\in H$, $r_2,\dots,r_d\in\mathbb K$ there is $Y\subseteq D$ with
--   $$|Y|=\frac{|D|}2,\qquad \sum_{y\in Y}y^j=r_j\quad(1\le j\le d)\qquad(37).$$
--
--   The completion hypothesis is a hypothesis of the source theorem; it is supplied later by Theorem 5.2. The fixed cardinality $|D|/2$ is what makes the final subset size exactly $n/2$.
--
--   Differences from the source:
--   - encoding: the standing setting of §6.1 (q prime, K = F_q[Z]/(P) with P monic irreducible of degree 2t+1, H = span{1, …, θ^t}) → explicit hypotheses on q, t ≥ 1 and P : Polynomial (ZMod q); K = AdjoinRoot P; reason: AdjoinRoot is the polynomial quotient with the power-basis coordinates of §6.1; primality, monicity, irreducibility and degree are explicit
--   - generalization: §6 opens with t = 2m from the nonempty cubic planar source formula and the field P constructed in §6.1 → every t ≥ 1 and every monic irreducible P of degree 2t+1 over the prime field; reason: every source field is included by taking t = 2m and its constructed P; the algebraic assertions use only the displayed power basis, and the condenser proof explicitly handles t = 1
--   - encoding: indexed targets c_1, …, c_d (or r_1, …, r_d) → a function on ℕ of which only the values at 1, …, d are used; reason: same instances; avoids Fin-indexed casts
--   - encoding: D = ⨆_{β∈B} βF_q^× and |Y| = |D|/2 → the finite set of c·β, c = 1..q−1, β ∈ B, and 2|Y| = |D|; reason: same set; |D| is even since |B| is
--   - encoding: h-element subset of F_q^× → finite set S of ZMod q with 0 ∉ S and |S| = h; reason: same sets
-- source:
--   Daqing Wan, Jun Zhang, NP-Hardness of Bounded Distance Decoding for Reed–Solomon Codes, STOC 2027 submission #449 (October 2026), Theorem 7.1; setting of §7, PDF p. 22, eq. (36), PDF p. 23 (printed p. 22); PDF SHA-256 d60d9a54b73aa972494f130439dc6e07f8c7b33556741f8324d22cf45218e22b

import Mathlib
import Definitions.Def_RSBDDHardness_PolyGap_Algebra
set_option autoImplicit false
open scoped BigOperators
open Classical

namespace RSBDDHardness.PolyGap

/-- Theorem 7.1 (Balanced universal completion), PDF 23 (setting PDF 22). Let `B ⊂ H ∖ {0}`
be projectively distinct of even size satisfying (31) and (32), `D = ⨆_{β∈B} β𝔽_q^×`, `q`
prime, `1 ≤ d < q − 1`. If for a fixed `1 ≤ h < q` every vector of `𝔽_q^d` is the first `d`
moments of an `h`-element subset of `𝔽_q^×`, then for every residual `r_1 ∈ H`,
`r_2, …, r_d ∈ 𝕂` some `Y ⊆ D` has `|Y| = |D|/2` and `∑_{y∈Y} y^j = r_j`, `1 ≤ j ≤ d`. -/
theorem theorem_7_1 (q t d h : ℕ) (P : Polynomial (ZMod q)) (hq : q.Prime) (ht : 1 ≤ t)
    (hP : P.Monic) (hirr : Irreducible P) (hdeg : P.natDegree = 2 * t + 1)
    (B : Finset (AdjoinRoot P)) (hB : IsDirectionSet P t d B) (hBeven : Even B.card)
    (hd1 : 1 ≤ d) (hdq : d < q - 1) (hh1 : 1 ≤ h) (hhq : h < q)
    (hcomp : ∀ c : ℕ → ZMod q, ∃ S : Finset (ZMod q),
      (0 : ZMod q) ∉ S ∧ S.card = h ∧ RealizesMoments S d c) :
    ∀ r : ℕ → AdjoinRoot P, r 1 ∈ Hsp P t →
      ∃ Y : Finset (AdjoinRoot P), Y ⊆ pool P B ∧ 2 * Y.card = (pool P B).card ∧
        RealizesMoments Y d r := by sorry

end RSBDDHardness.PolyGap
