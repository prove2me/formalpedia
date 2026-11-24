-- Prove2me | Theorems.Thm_PalomaMax2SAT_UgcStrong_strong_ugc_broken
-- name    : PalomaMax2SAT.UgcStrong.strong_ugc_broken
-- status  : Proved
-- author  : @vegafrank
-- created : 2026-11-24T08:10:23.015805+00:00
-- url     : https://prove2.me/theorems/b38fd0c1-493b-4d8f-a94d-85541305e1eb
-- title:
--   The strong bounded-degree UGC barrier for MAX-E2LIN(2) is exceeded for all degrees d >= 1
-- statement:
--   Let $\alpha_{\mathrm{GW}}=0.87856$, $\beta^\star=0.94016567$ and $\alpha^*=0.94615981$. Then $\alpha_{\mathrm{GW}}<\beta^\star<\alpha^*<\tfrac{83}{84}<0.9932$. (1) For every rational $a\ge 0.8785$, $1-\frac{1-a}{18}>0.9932$, and for every $d\ge 1$, $1-\frac{1-a}{6d+12}>0.9932$; hence every threshold $\tau\le 0.9932$ is strictly below these ratios. (2) For every $\varepsilon>0$ there is $D$ with $1-\varepsilon<1-\frac{1-a}{6d+12}$ for all $d\ge D$. (3) $0.9326-0.87856=0.05404>0$. (4) If $mc\le m$, $p\le q$ and $p\,mc\le q\,\mathrm{cut}$, then with $B=m(6d+10)$, $\alpha=m+mc$, $s=m+\mathrm{cut}$: $(6d+12)q(B+\alpha)\le(6d+12)q(B+s)+(q-p)(B+\alpha)$, i.e. the lifted ratio is at least $1-\frac{1-p/q}{6d+12}$. (5) $\alpha(H(G))=m+\mathrm{maxcut}(G)$; if $G$ has maximum degree at most $D$ then $H(G)$ has maximum degree at most $D+1$; $2M=4m+2\sum_v\deg(v)^2$ and $4m\le M$ for the number $M$ of edges of $H(G)$; and $4m\le M$, $\alpha\le 2m$, $18785\alpha\le 20000 s$ imply $9932(B+\alpha)\le 10000(B+s)$ for $B=4m+3M$. (6) For a port graph of degree 1 the independence number is $m$ and the optimum of $T_H$ is $3n$; for degree 2, $m=n$ and the optimum is $4n+\alpha$. The value of $\tau_{\mathrm{strong}}(d)=\alpha_{\mathrm{GW}}+\widetilde O(1/d)$, the Goemans--Williamson and Halperin--Livnat--Zwick guarantees, the polynomial running times and the Unique Games hardness statements are cited in the paper and are not formalized.
-- source:
--   https://github.com/frankvegadelgado/paloma/blob/strong-ugc-broken/doc/paper.tex#L179

import Mathlib
import Definitions.Def_PalomaMax2SAT_UgcStrong_Defs

theorem PalomaMax2SAT.UgcStrong.strong_ugc_broken :
    (87856 : ℚ) / 100000 < 94016567 / 100000000 ∧
    (94016567 : ℚ) / 100000000 < 94615981 / 100000000 ∧
    (94615981 : ℚ) / 100000000 < 83 / 84 ∧
    (83 : ℚ) / 84 < 9932 / 10000 ∧
    (∀ x : ℚ, (8785 : ℚ) / 10000 ≤ x →
      (9932 : ℚ) / 10000 < 1 - (1 - x) / 18 ∧
        ∀ t : ℚ, t ≤ 9932 / 10000 → t < 1 - (1 - x) / 18) ∧
    (∀ x : ℚ, (8785 : ℚ) / 10000 ≤ x → ∀ d : ℕ, 1 ≤ d →
      (9932 : ℚ) / 10000 < 1 - (1 - x) / (6 * d + 12) ∧
        ∀ t : ℚ, t ≤ 9932 / 10000 → t < 1 - (1 - x) / (6 * d + 12)) ∧
    (∀ x : ℚ, (8785 : ℚ) / 10000 ≤ x → ∀ e : ℚ, 0 < e →
      ∃ D : ℕ, ∀ d : ℕ, D ≤ d → 1 - e < 1 - (1 - x) / (6 * d + 12)) ∧
    ((87856 : ℚ) / 100000 < 9326 / 10000 ∧
      (9326 : ℚ) / 10000 - 87856 / 100000 = 5404 / 100000) ∧
    (∀ d m mc cut p q : ℕ, mc ≤ m → p ≤ q → p * mc ≤ q * cut →
      (6 * d + 12) * q * (m * (6 * d + 10) + (m + mc)) ≤
        (6 * d + 12) * q * (m * (6 * d + 10) + (m + cut)) +
          (q - p) * (m * (6 * d + 10) + (m + mc))) ∧
    (∀ {n m mc : ℕ} (G : PalomaMax2SAT.CutTransfer.EdgeGraph n m),
      PalomaMax2SAT.ConflictGraph.IsMaxCut G mc →
        PalomaMax2SAT.ConflictGraph.IsIndNumber G (m + mc)) ∧
    (∀ {n m : ℕ} (G : PalomaMax2SAT.CutTransfer.EdgeGraph n m) (Dmax : ℕ),
      (∀ v, PalomaMax2SAT.ConflictDegree.occ G v ≤ Dmax) →
        ∀ p : PalomaMax2SAT.ConflictGraph.Occ m,
          (PalomaMax2SAT.ConflictDegree.nbrs G p).card ≤ Dmax + 1) ∧
    (∀ {n m : ℕ} (G : PalomaMax2SAT.CutTransfer.EdgeGraph n m) (M : ℕ),
      2 * M = ∑ p : PalomaMax2SAT.ConflictGraph.Occ m,
          (PalomaMax2SAT.ConflictDegree.nbrs G p).card →
        2 * M = 4 * m + 2 * ∑ v, PalomaMax2SAT.ConflictDegree.occ G v ^ 2 ∧ 4 * m ≤ M) ∧
    (∀ m M alpha s : ℕ, 4 * m ≤ M → alpha ≤ 2 * m → 18785 * alpha ≤ 20000 * s →
      9932 * ((4 * m + 3 * M) + alpha) ≤ 10000 * ((4 * m + 3 * M) + s) ∧
        83 * ((4 * m + 3 * M) + alpha) ≤ 84 * ((4 * m + 3 * M) + s)) ∧
    (∀ {n m alpha : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph 1 n m),
      PalomaMax2SAT.DegreeFormula.IsIndependenceNumber G alpha →
        alpha = m ∧
          IsGreatest (Set.range (PalomaMax2SAT.DegreeFormula.satCount G)) (3 * n)) ∧
    ∀ {n m alpha : ℕ} (G : PalomaMax2SAT.DegreeFormula.PortGraph 2 n m),
      PalomaMax2SAT.DegreeFormula.IsIndependenceNumber G alpha →
        m = n ∧
          IsGreatest (Set.range (PalomaMax2SAT.DegreeFormula.satCount G)) (4 * n + alpha) := by sorry
