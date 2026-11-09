-- Prove2me | Theorems.Thm_ResPCDegreeSize_Main_equations_55_56
-- name    : ResPCDegreeSize.Main.equations_55_56
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:26:15.924723+00:00
-- url     : https://prove2.me/theorems/372cd265-8854-497b-8b38-a97c51a937d6
-- title:
--   Section 6, eqs. (54)–(56) — the parameter computation
-- statement:
--   Let $p$ be prime, $r\ge1$, $d=(p-1)r$, $\Delta=(p-1)dt$, and take
--   $$K=\Bigl\lfloor\frac D4\Bigr\rfloor,\qquad t=\Bigl\lfloor\frac{D}{8(p-1)d}\Bigr\rfloor.$$
--   Suppose $D\ge\max\{32(p-1)^2r,8w\}$ and $D\le n$. Then $\Delta\le D/8$, $K\ge2d$, $K\le n/3$, $N_n(K)\le2\binom nK$, and
--   $$\frac{N_n(K-d)}{N_n(K)}\ge\frac{\binom{n}{K-d}}{2\binom nK}=\frac12\prod_{j=0}^{d-1}\frac{K-j}{n-K+j+1}\ge\frac12\Bigl(\frac K{2n}\Bigr)^d\ge\frac12\Bigl(\frac D{16n}\Bigr)^d.\tag{55}$$
--   For $\eta=(1-\frac1p)N_n(K-d)/N_n(K)$,
--   $$\eta t\ge\frac{D}{32pd}\Bigl(\frac{D}{16n}\Bigr)^d.\tag{56}$$
--
--   This is the numerical core of the main theorem: it turns the rank decay of Theorem 4.3 into the explicit bound.
--
--   Differences from the source:
--   - encoding: K = ⌊D/4⌋, t = ⌊D/(8(p−1)d)⌋, Δ ≤ D/8, K ≤ n/3 → natural-number division, and 8((p−1)dt) ≤ D, 3K ≤ n; reason: floor division of naturals is the floor, and the inequalities are cleared of denominators
--   - generalization: D ≤ n obtained from Q(F) ⊬_D 1, and w = w(F) → D ≤ n as a hypothesis and w an arbitrary natural number; reason: the computation is numeric; the first paragraph of Section 6 (item section_6_degree_le_n) supplies D ≤ n, so the source's case is an instance
-- source:
--   Pang, A Degree–Size Relation for Resolution over Polynomials, 2026 preprint (STOC 2027 submission #128; SHA-256 d026926040f9df67b9f5a3212fe878d8a10b50dd70b04f14b63b62a9dcb9d32f), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/128.pdf, Section 6, eqs. (54)–(56), PDF p. 11 (printed p. 10)

import Mathlib
import Definitions.Def_ResPCDegreeSize_Main_RankMaps

namespace ResPCDegreeSize.Main

theorem equations_55_56 {p r n D w d K t : ℕ} [Fact p.Prime] (hr : 1 ≤ r)
    (hd : d = (p - 1) * r) (hK : K = D / 4) (ht : t = D / (8 * (p - 1) * d))
    (hD : max (32 * (p - 1) ^ 2 * r) (8 * w) ≤ D) (hDn : D ≤ n) :
    8 * ((p - 1) * d * t) ≤ D ∧
    2 * d ≤ K ∧
    3 * K ≤ n ∧
    Nn n K ≤ 2 * n.choose K ∧
    (n.choose (K - d) : ℝ) / (2 * (n.choose K : ℝ)) ≤ (Nn n (K - d) : ℝ) / (Nn n K : ℝ) ∧
    (n.choose (K - d) : ℝ) / (2 * (n.choose K : ℝ)) =
      1 / 2 * ∏ j ∈ Finset.range d, ((K : ℝ) - j) / ((n : ℝ) - K + j + 1) ∧
    1 / 2 * ((K : ℝ) / (2 * n)) ^ d ≤
      1 / 2 * ∏ j ∈ Finset.range d, ((K : ℝ) - j) / ((n : ℝ) - K + j + 1) ∧
    1 / 2 * ((D : ℝ) / (16 * n)) ^ d ≤ 1 / 2 * ((K : ℝ) / (2 * n)) ^ d ∧
    (D : ℝ) / (32 * p * d) * ((D : ℝ) / (16 * n)) ^ d ≤ eta p n K d * t := by sorry

end ResPCDegreeSize.Main
