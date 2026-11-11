-- Prove2me | Theorems.Thm_RSBDDHardness_PolyGap_theorem_8_1
-- name    : RSBDDHardness.PolyGap.theorem_8_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:28:32.738185+00:00
-- url     : https://prove2.me/theorems/a0a3fdd2-5154-4554-a2f4-de753db67cad
-- title:
--   Theorem 8.1 — correctness of the §8 reduction to moments subset sum
-- statement:
--   Fix a rational $\rho>0$ and positive integers $\nu,C$ with $C>2+2/\rho$. There is a padding threshold $t_0$ such that the following holds for every cubic monotone Exact 1-in-3 formula $\varphi$ with $m$ variables and $t=2m\ge t_0$. Put $d_0=t^\nu$, $h=Cd_0$ and $Q_0$ as in (39). Let $q$ be any prime with $Q_0\le q\le 2Q_0$ (40), $P\in\mathbb F_q[Z]$ any monic irreducible polynomial of degree $2t+1$, and $B$ any projectively distinct set $B\subseteq H\setminus\{0\}$ with (31), (32) for the cutoff $d_0$ and $|B|=2t+2$ (as produced by Lemma 6.3). For the instance $(A,k,M_1,\dots,M_{d_0})$ of §8.1,
--   $$\varphi\text{ is Exact 1-in-3 satisfiable}\iff\exists S\subseteq A,\ |S|=k,\ \sum_{x\in S}x^j=M_j\ (1\le j\le d_0).$$
--
--   This is the correctness of the deterministic reduction; the completing subset in the forward direction is supplied by Theorems 5.2 and 7.1, and the backward direction uses only the first moment.
--
--   Differences from the source:
--   - generalization: constants ρ, ν, C fixed together with α subject to (38), including α < ν/(1+ν(2+ρ)) → any rational ρ > 0 and integers ν ≥ 1, C > 2 + 2/ρ (no condition involving α); reason: the α-condition only enters the size analysis of §8.3; every admissible choice of (38) satisfies these hypotheses
--   - generalization: P produced by Shoup’s algorithm and B produced by Lemma 6.3 → every monic irreducible P of degree 2t+1 and every B with the properties of Lemma 6.3 (|B| = 2t+2); reason: the constructed P and B are instances of the quantified ones
--   - generalization: the padded formula is cubic planar monotone Exact 1-in-3-SAT (§8.1) → any nonempty cubic monotone formula, without an incidence-planarity hypothesis; reason: §3.4 explicitly says the reduction does not use planarity; every padded source formula satisfies IsCubic
--   - reading: a fixed padding threshold t₀ chosen large enough (§8.1, Preprocessing) → existence of t₀ with the conclusion for every formula with t ≥ t₀; reason: the threshold is existential in the source; the size conditions on t₀ belong to Theorem 2.1
--   - encoding: t = 2m → t = m + c with c = m for cubic formulas; reason: same value
-- source:
--   Daqing Wan, Jun Zhang, NP-Hardness of Bounded Distance Decoding for Reed–Solomon Codes, STOC 2027 submission #449 (October 2026), Theorem 8.1 with the construction of §8.1, eqs. (38)–(43), PDF pp. 23–26, PDF p. 26 (printed p. 25); PDF SHA-256 d60d9a54b73aa972494f130439dc6e07f8c7b33556741f8324d22cf45218e22b

import Mathlib
import Definitions.Def_RSBDDHardness_PolyGap_Algebra
import Definitions.Def_RSBDDHardness_PolyGap_Construction
set_option autoImplicit false
open scoped BigOperators
open Classical

namespace RSBDDHardness.PolyGap

/-- Theorem 8.1 (Reduction correctness), PDF 26, with the construction of §8.1 (PDF 23–26).
Fix a rational `ρ > 0` and integers `ν ≥ 1`, `C > 2 + 2/ρ`. There is a padding threshold `t₀`
such that for every cubic monotone formula `φ` with `t = 2m ≥ t₀`, `d₀ = t^ν`, every prime
`q` with `Q₀ ≤ q ≤ 2Q₀` (39)–(40), every monic irreducible `P ∈ 𝔽_q[Z]` of degree `2t+1` and
every direction set `B` as in Lemma 6.3 (cutoff `d₀`, `|B| = 2t+2`), `φ` is satisfiable iff the
MSS instance `(A, k, M_1, …, M_{d₀})` of Step 6 has a solution. -/
theorem theorem_8_1 (ρ : ℚ) (ν C : ℕ) (hρ : 0 < ρ) (hν : 1 ≤ ν) (hC : 2 + 2 / (ρ : ℝ) < C) :
    ∃ t₀ : ℕ, ∀ φ : OneInThree, φ.IsCubic → t₀ ≤ Sec8.t φ →
      ∀ q : ℕ, q.Prime →
        sec8Q0 ρ C (sec8d0 (Sec8.t φ) ν) ≤ q → q ≤ 2 * sec8Q0 ρ C (sec8d0 (Sec8.t φ) ν) →
      ∀ P : Polynomial (ZMod q), P.Monic → Irreducible P → P.natDegree = 2 * Sec8.t φ + 1 →
      ∀ B : Finset (AdjoinRoot P), IsDirectionSet P (Sec8.t φ) (sec8d0 (Sec8.t φ) ν) B →
        B.card = 2 * Sec8.t φ + 2 →
        (φ.Satisfiable ↔
          MSS (Sec8.univA φ q P B) (Sec8.size φ q P B) (sec8d0 (Sec8.t φ) ν)
            (Sec8.targets φ q P)) := by sorry

end RSBDDHardness.PolyGap
