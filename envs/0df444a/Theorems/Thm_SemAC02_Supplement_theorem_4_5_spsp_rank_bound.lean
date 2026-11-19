-- Prove2me | Theorems.Thm_SemAC02_Supplement_theorem_4_5_spsp_rank_bound
-- name    : SemAC02.Supplement.theorem_4_5_spsp_rank_bound
-- status  : Proved
-- author  : @iris
-- created : 2026-11-15T19:49:32.038284+00:00
-- url     : https://prove2.me/theorems/9b4430ec-7464-4a2f-91e8-d4c33d3e95d3
-- title:
--   Theorem 4.5 — rank bound for ΣΠΣΠ[w]-PC with n-divisions
-- statement:
--   Let $F\subseteq B_N$ have an $n$-division $V_1,\dots,V_n$ with parts of size $h$, $N=nh$, and let $F_0\subseteq F$ be the set of products $xy$ of distinct variables of the same part. Consider $F$ in $B_{F_0}=B_N/\langle F_0\rangle$ and suppose its axioms have degree at most $d_0$ there. Fix integers $w\ge1$, $2w\le k\le n$ and $r\ge0$, and put $B=3(k+\max\{d_0,rw\})$. Suppose that $B\le n$ and that $R:B_{F_0}^{\le B}\to W$ is a degree-$B$ pseudo-reduction operator for $F$, with restriction $R_{\le k}$ to $B_{F_0}^{\le k}$. Then every arity-2 semantic ΣΠΣΠ[$w$]-PC refutation $\pi$ of $F$ satisfies
--
--   $$
--   S(\pi)\ \ge\ \frac{\operatorname{rank}(R_{\le k})}{2\binom nk h^k}\,\exp\!\Bigl(\frac r4\Bigl(\frac k{2N}\Bigr)^{w}\Bigr),
--   $$
--
--   where $S(\pi)$ counts the distinct non-zero classes in $B_{F_0}$ of the top product terms.
--
--   It is the bounded-bottom-fan-in counterpart of Theorem 4.4, applied in §7 to random log-width CNFs and graph PHP.
--
--   **Formalization Note** Variables are $(i,j)$, $i\in[n]$, $j\in[h]$; $B_{F_0}$ is the algebra of functions on $\Omega$, the points with at most one $1$ per part.
--
--   Differences from the source:
--   - encoding: proof lines are displayed circuits representing classes in B_n; initial lines are the axioms → ACirc terms; a line is an axiom line when its value on the cube equals an axiom; initial lines equal to 0 are allowed; reason: p.15: a line represents its residue class; p.54: initial tautologies 0 = 0; a zero line follows from any line, so no refutation or measure changes
--   - reading: semantic refutation of F considered in B_{F0} → refutation modulo F₀: inferences sound on Ω, axiom lines equal on Ω to an axiom, last line 1 on Ω; reason: p.24: semantic inferences are interpreted on Ω; every ordinary refutation is one, and its S modulo F₀ is no larger
--   - encoding: n-division V₁, …, V_n of N = nh variables → variables Fin n × Fin h, V_i = {i} × Fin h; reason: relabelling of the variables
--   - encoding: every part has size h, N = nh (the bound contains k/(2N), so h ≥ 1) → h : ℕ unrestricted; at h = 0 the real division by (h:ℝ)^k = 0 makes the left side 0 and the statement reads 0 ≤ S(π); reason: excludes only the case where the printed bound is undefined; every instance with h ≥ 1 is the source statement
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Theorem 4.5, pp.26–27 (PDF pp.28–29)

import Mathlib
import Definitions.Def_SemAC02_Ble
import Definitions.Def_SemAC02_nDivision
import Definitions.Def_SemAC02_Supplement_ACirc
import Definitions.Def_SemAC02_Supplement_IsSemPCRef
import Definitions.Def_SemAC02_Supplement_IsPseudoRed

namespace SemAC02.Supplement

open MvPolynomial ACirc

/-- **Theorem 4.5 (Rank bound for ΣΠΣΠ[w]-PC with n-divisions)** (Alekseev–Gryaznov–Itsykson–
Pitassi–Robere–Tzameret, *Hard Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027
submission), Theorem 4.5, pp.26–27): let `F ⊆ B_N` have an `n`-division `V₁, …, V_n`, every part
of size `h`, `N = nh`. Let `F₀ ⊆ F` be the set of all products `xy` of distinct variables from the
same part. Consider `F` in the quotient `B_{F₀} = B_N/⟨F₀⟩`, and suppose that its axioms have
degree at most `d₀` there. Fix integers `w ≥ 1`, `2w ≤ k ≤ n`, and `r ≥ 0`, and put
`B = 3(k + max{d₀, rw})`. Suppose that `B ≤ n` and that `R : B_{F₀}^{≤B} → W` is a degree-`B`
pseudo-reduction operator for `F`. Write `R_{≤k}` for the restriction of `R` to `B_{F₀}^{≤k}`.
Then every semantic ΣΠΣΠ[w]-PC refutation `π` of `F` satisfies
`S(π) ≥ rank(R_{≤k}) / (2 C(n, k) h^k) · exp((r/4)(k/(2N))^w)`.

**Formalization Note** The variables are `Fin n × Fin h`, part `V_i = {i} × [h]`. `B_{F₀}` is the
algebra of functions on `Ω = nDivOmega n h` (the published `restrOmega`, `BleF0`). As stated on
p.24 ("semantic inferences are interpreted on `Ω`"), the refutation is taken modulo `F₀`
(inferences sound on `Ω`, axiom lines equal on `Ω` to an axiom), which includes every ordinary
refutation; `S(π)` counts distinct non-zero classes in `B_{F₀}` of the top product terms. -/
theorem theorem_4_5_spsp_rank_bound {n h : ℕ} (F : Set (MvPolynomial (Fin n × Fin h) (ZMod 2)))
    (hdiv : ∀ (i : Fin n) (j j' : Fin h), j ≠ j' → X (i, j) * X (i, j') ∈ F)
    (d₀ : ℕ) (hdeg : ∀ f ∈ F, restrOmega n h f ∈ BleF0 n h d₀)
    (w k r : ℕ) (hw : 1 ≤ w) (hwk : 2 * w ≤ k) (hkn : k ≤ n)
    (hB : 3 * (k + max d₀ (r * w)) ≤ n)
    {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (R : BleF0 n h (3 * (k + max d₀ (r * w))) →ₗ[ZMod 2] W) (hR : IsPseudoRedF0 F R)
    (π : List (ACirc (ZMod 2) (Fin n × Fin h)))
    (hπ : IsSemPCRef (IsSPSP (w : ℕ∞)) (nDivOmega n h) (polyAx F) π) :
    (rankLeF0 R k : ℝ) / (2 * (n.choose k : ℝ) * (h : ℝ) ^ k) *
        Real.exp ((r : ℝ) / 4 * ((k : ℝ) / (2 * ((n : ℝ) * h))) ^ w) ≤
      topS (nDivOmega n h) π := by sorry

end SemAC02.Supplement
