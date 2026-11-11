-- Prove2me | Theorems.Thm_PrefixMixLearn_Proper_theorem_d_2
-- name    : PrefixMixLearn.Proper.theorem_d_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:47:35.96165+00:00
-- url     : https://prove2.me/theorems/be9474e1-eeec-411d-9645-7242d64d327b
-- title:
--   Theorem D.2 — joint weak-view unmixing: proper M̂_A with error 2^20(L+1)η/u², and the raw contract (D.4) on one event
-- statement:
--   Setting: $0<\alpha<1/2$, $u=\alpha(1-\alpha)$; the view $A=\{0,1\}^d$ ($d\ge1$) and a finite future view $B$; comparator $M_{AB}=(1-w)Q_\nu\otimes R_0+wQ_\mu\otimes R_1$ with $0<w<1$, $\mu,\nu\in[\alpha,1-\alpha]^d$ and laws $R_0,R_1$ on $B$; a full-support law $P_{AB}$; a test $e:B\to[0,1]$; $a=E_{R_0}e$, $b=E_{R_1}e$, $g=b-a>0$, $q=w(1-w)$, $r=\|\mu-\nu\|_2$, $\eta=d_{TV}(P_{AB},M_{AB})$; signed unmixings $N_0,N_1$, $w'$ and raw profiles $\tilde\nu,\tilde\mu$ as in the Unmixing definitions. Fix $L\ge1$ and assume
--   $$r\le\sqrt u/64,\qquad r\le Lg,\qquad \eta\le2^{-20}qg^2.$$
--   Then the construction $\hat M_A(x)$ (uniform fallback, else restoration of $(\tilde\nu,\tilde\mu)$ at weight $w'$) is a proper balanced mixture on every path $x$; there is one event $G$ with $P_A(G)\ge81/128-\eta>1/2$ on which simultaneously
--   $$d_{TV}(P_A,\hat M_A)\le\frac{2^{20}(L+1)}{u^2}\eta,\quad \|\tilde d-(\mu-\nu)\|_2\le\frac{512\eta}{qg\sqrt\alpha},\quad \|(1-w')(\tilde\nu-\nu)+w'(\tilde\mu-\mu)\|_2\le\frac{2^{15}(L+1)}{u}\eta,$$
--   $|w'-w|\le\eta/g$, and $N_0[h]/P_A[h]\ge(1-w)/4$, $N_1[h]/P_A[h]\ge w/4$ for every parent prefix $h=x_{\le t}$, $0\le t<d$; and for $\eta=0$ the raw errors vanish on every path. No lower bound on $w$, $g$ or separation beyond (D.2) is used. This is the analytic core of the weak-separation case of the learner.
--
--   Differences from the source:
--   - generalization: B a finite future view; laws R_0, R_1 on it → any finite type Y with laws R0 R1 : Y → ℝ; P_AB a full-support law on Cube d × Y; reason: the proof uses only that the future view is a finite set carrying the laws R_0, R_1, P_AB and the test e; a future view B of the cube is the finite set {0,1}^B, so the statement specializes to the source
--   - encoding: the scalars a, b, η named in the setting → real variables with defining hypotheses a = testMean R0 e, b = testMean R1 e, η = tv P_AB M_AB; reason: same values; makes the statement readable
--   - reading: succeeds with probability at least 1/2 … there is one common-path event G with P_A(G) ≥ 81/128 − η > 1/2 on which the proper conclusion and all the raw guarantees hold → properness on every path; 1/2 < 81/128 − η; ∃ G with P_A(G) ≥ 81/128 − η on which (D.3) and every bound of (D.4) hold; reason: the success event is G; the probability-1/2 sentence is the consequence 81/128 − η > 1/2
--   - reading: for η = 0 the raw errors vanish on every path → η = 0 → for every x: D_dir = 0, E_mean = 0 and w′ = w; reason: the raw errors are the three error quantities of (D.4); the denominator floors are asserted only on G, as the source says
--   - encoding: coordinates i = 1, …, T; laws on {0,1}^T → `Fin T`, coordinate i ↦ i.val + 1; laws are real functions on `Fin T → Bool` with `IsLaw`; reason: Lean convention; same statement
-- source:
--   Saravanan, Proper Agnostic Learning of Two Balanced Product Distributions from Prefix-Conditional Samples, STOC 2027 submission (manuscript sha256 9c359910…), p. 31 (PDF 33), Theorem D.2, (D.2)–(D.4)

import Mathlib
import Definitions.Def_PrefixMixLearn_Proper_Laws
import Definitions.Def_PrefixMixLearn_Proper_Geometry
import Definitions.Def_PrefixMixLearn_Proper_Unmixing

namespace PrefixMixLearn.Proper

/-- Theorem D.2 (joint weak-view unmixing). Setting of §D.2: view `A = {0,1}^d`, finite future
view `Y`, comparator `M_AB = (1 − w)Q_ν ⊗ R_0 + wQ_μ ⊗ R_1` with `0 < w < 1`, `μ, ν` balanced,
full-support `P_AB`, test `e : Y → [0,1]`, `a = E_{R_0} e`, `b = E_{R_1} e`, `g = b − a > 0`,
`q = w(1 − w)`, `u = α(1 − α)`, `r = ‖μ − ν‖₂`, `η = d_TV(P_AB, M_AB)`, `L ≥ 1`. Under
`r ≤ √u/64`, `r ≤ Lg`, `η ≤ 2^{-20} q g²` (D.2): the construction is proper on every path; there is
one event `G` with `P_A(G) ≥ 81/128 − η > 1/2` on which (D.3) and every raw bound of (D.4) hold;
and for `η = 0` the raw errors vanish on every path. -/
theorem theorem_d_2 (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1 / 2) (d : ℕ) (hd : 1 ≤ d)
    {Y : Type*} [Fintype Y]
    (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1) (ν μ : Fin d → ℝ) (hν : InBox α ν) (hμ : InBox α μ)
    (R0 R1 : Y → ℝ) (hR0 : IsLaw R0) (hR1 : IsLaw R1)
    (PAB : Cube d × Y → ℝ) (hP : IsLaw PAB) (hPf : FullSupport PAB)
    (e : Y → ℝ) (he : ∀ y, 0 ≤ e y ∧ e y ≤ 1)
    (a b : ℝ) (ha : a = testMean R0 e) (hb : b = testMean R1 e) (hg : 0 < b - a)
    (η : ℝ) (hηdef : η = tv PAB (condProdMix w ν μ R0 R1))
    (L : ℝ) (hL : 1 ≤ L)
    (hr1 : l2 (fun i => μ i - ν i) ≤ Real.sqrt (uOf α) / 64)
    (hr2 : l2 (fun i => μ i - ν i) ≤ L * (b - a))
    (hη : η ≤ (2 : ℝ) ^ (-20 : ℤ) * (w * (1 - w)) * (b - a) ^ 2) :
    (∀ x : Cube d, weakViewEstimate α PAB e a b x ∈ M2Class α d) ∧
    1 / 2 < 81 / 128 - η ∧
    (∃ G : Set (Cube d), 81 / 128 - η ≤ massOf (marginalA PAB) G ∧
      ∀ x ∈ G,
        tv (marginalA PAB) (weakViewEstimate α PAB e a b x) ≤
            (2 : ℝ) ^ 20 * (L + 1) / uOf α ^ 2 * η ∧
        l2 (fun i => (rawProfile (unmixN1 PAB e a b) x i - rawProfile (unmixN0 PAB e a b) x i)
            - (μ i - ν i)) ≤ 512 * η / (w * (1 - w) * (b - a) * Real.sqrt α) ∧
        l2 (fun i => (1 - wPrime PAB e a b) * (rawProfile (unmixN0 PAB e a b) x i - ν i)
            + wPrime PAB e a b * (rawProfile (unmixN1 PAB e a b) x i - μ i)) ≤
            (2 : ℝ) ^ 15 * (L + 1) / uOf α * η ∧
        |wPrime PAB e a b - w| ≤ η / (b - a) ∧
        ∀ t : ℕ, t < d →
          (1 - w) / 4 ≤ prefMass (unmixN0 PAB e a b) x t / prefMass (marginalA PAB) x t ∧
          w / 4 ≤ prefMass (unmixN1 PAB e a b) x t / prefMass (marginalA PAB) x t) ∧
    (η = 0 → ∀ x : Cube d,
      l2 (fun i => (rawProfile (unmixN1 PAB e a b) x i - rawProfile (unmixN0 PAB e a b) x i)
          - (μ i - ν i)) = 0 ∧
      l2 (fun i => (1 - wPrime PAB e a b) * (rawProfile (unmixN0 PAB e a b) x i - ν i)
          + wPrime PAB e a b * (rawProfile (unmixN1 PAB e a b) x i - μ i)) = 0 ∧
      wPrime PAB e a b = w) := by sorry

end PrefixMixLearn.Proper
