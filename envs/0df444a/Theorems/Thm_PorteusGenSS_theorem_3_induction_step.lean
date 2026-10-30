-- Prove2me | Theorems.Thm_PorteusGenSS_theorem_3_induction_step
-- name    : PorteusGenSS.theorem_3_induction_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:20:26.979271+00:00
-- url     : https://prove2.me/theorems/26e23f7d-62c7-4f8f-9db7-f91e13117a28
-- title:
--   Proof of Theorem 3: conditions (i)–(iii) of Lemma 3 pass from $f_{k-1}$ to $f_k$
-- statement:
--   Standing assumptions: $c$ is concave and nondecreasing on $[0,\infty)$ with $c(0)=0$, and its tangent parameters converge, $C_2(z)\to(c_0,K_0)$ as $z\downarrow0$ and $C_2(z)\to(c_\infty,K_\infty)$ as $z\to\infty$; $0\le\alpha\le1$; $\varphi$ is a one-sided Pólya density; $m$ is measurable, PF-integrable and bounded below. Assumptions A1–A4:
--
--   - A1. $x\mapsto(c_0-\alpha c_\infty)x+m(x)$ is nonincreasing on $(-\infty,0)$;
--   - A2. $(c_0-\alpha c_\infty)x+m(x)\to\infty$ as $x\to-\infty$;
--   - A3. for every $a\in C$, $x\mapsto(1-\alpha)a x+m(x)$ is non-$(1-\alpha)K_a$-decreasing on $[0,\infty)$;
--   - A4. $(1-\alpha)c_\infty x+m(x)\to\infty$ as $x\to\infty$.
--
--   Let $F$ (the paper's $f_{n-1}$) satisfy (i) $F$ is piecewise continuous and PF-integrable, (ii) $x\mapsto c_\infty x+F(x)$ is nonincreasing on $(-\infty,0)$, (iii) for every $a\in C$, $x\mapsto ax+F(x)$ is non-$K_a$-decreasing on $\mathbb R$.
--
--   Let $h=(m+\alpha F)*\varphi$ and $F'(x)=\inf_{w\ge x}\{c(w-x)+h(w)\}$ (the paper's $f_k$, with $F=f_{k-1}$). Then $F'$ satisfies (i)–(iii) as well:
--
--   1. $F'$ is piecewise continuous and PF-integrable;
--   2. $x\mapsto c_\infty x+F'(x)$ is nonincreasing on $(-\infty,0)$;
--   3. for every $a\in C$, $x\mapsto ax+F'(x)$ is non-$K_a$-decreasing on $\mathbb R$.
--
--   This is the induction step in the proof of Theorem 3; with A5 as base case it gives (i)–(iii) for every $f_n$. No continuity of $m$ is assumed.
--
--   Differences from the source:
--
--   - encoding: hn = L + αfn−1∗φ → conv (fun x => m x + α * F x) φ; reason: the second form (m + αfn−1)∗φ of (3), as printed
--   - encoding: fn(x) = inf_{y≥x}{c(y − x) + hn(y)} → valueOp: real ⨅ over Set.Ici x; reason: under the hypotheses the infimum is attained (Lemma 3), so the default value 0 is never reached
--   - encoding: for c ∈ C … K_c → ∀ a K, IsTangentPair c a K → …; reason: K_c is unique for its slope; same instances
--   - encoding: lim_{z↓0} C2(z) = (c0, K0), lim_{z→∞} C2(z) = (c∞, K∞) → C2Tendsto c (𝓝[>] 0) (c0, K0), C2Tendsto c atTop (cinf, Kinf) (set convergence); reason: C2(z) is a singleton for z > 0; same as the ordinary limit
--   - reading: c concave increasing → ConcaveOn and MonotoneOn on [0, ∞) (nondecreasing); reason: the paper never defines "increasing"; nondecreasing is the weaker hypothesis, so the theorem covers every strictly increasing c as well
--   - encoding: convolution integral ∫ f(y − ξ)g(ξ) dξ → Bochner integral conv (0 if not integrable); reason: the integrands here are integrable by PF-integrability, so the default is never reached
--   - encoding: m (Lebesgue) measurable (§X) → AEMeasurable m (for the Lebesgue measure volume); reason: a real function is Lebesgue measurable iff it agrees a.e. with a Borel function; same functions
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), proof of Theorem 3, p. 419 (unnumbered)

import Mathlib
import Definitions.Def_PorteusGenSS_IsOrderingCost
import Definitions.Def_PorteusGenSS_C2Tendsto
import Definitions.Def_PorteusGenSS_IsTangentPair
import Definitions.Def_PorteusGenSS_IsOneSidedPolyaDensity
import Definitions.Def_PorteusGenSS_PFIntegrable
import Definitions.Def_PorteusGenSS_PiecewiseContinuous
import Definitions.Def_PorteusGenSS_NonKDecreasingOn
import Definitions.Def_PorteusGenSS_conv
import Definitions.Def_PorteusGenSS_valueOp

open Filter Topology

namespace PorteusGenSS

/-- **Induction step of the proof of Theorem 3: (i)–(iii) of Lemma 3 pass from f_{k−1} to f_k.**
Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), proof of Theorem 3, p. 419 (unnumbered):
"The proof is by induction. We shall show that conditions (i)–(iii) of Lemma 3 hold for all
n ≥ 1. Then by Lemma 3 and Theorem 2, we achieve our desired result. By A5, (i)–(iii) hold for
n = 1. Suppose (i)–(iii) hold for n = k. We seek to prove that they hold for n = k + 1."

Under the standing assumptions of §II (p. 412: `c` concave increasing with `c(0) = 0`, the limits
`(c₀, K₀)` of `C₂(z)` as `z ↓ 0` and `(c_∞, K_∞)` as `z → ∞`), §III (p. 413: `0 ≤ α ≤ 1`, `φ` a
one-sided Pólya density, `m` PF-integrable and bounded below) and §X (p. 425: `m` (Lebesgue) measurable, i.e. `AEMeasurable m` for the Lebesgue measure) and A1–A4 (§VI, p. 417), suppose a function `F` (the paper's `f_{k−1}`)
satisfies (i) `F` is piecewise continuous and PF-integrable, (ii) `c_∞· + F` is nonincreasing on
`(−∞, 0)`, (iii) `c· + F` is non-`K_c`-decreasing on `ℝ` for `c ∈ C`. Then
`F′ = inf_{w ≥ x} (c(w − x) + h(w))` with `h = (m + αF)∗φ` (the paper's `f_k`) satisfies
(i)–(iii) as well.

**Formalization Note.** Conditions (i)–(iii) for `n = k + 1` concern `f_k`, which is
`valueOp c h_k` with `h_k = (m + αf_{k−1})∗φ` ((3), (4), p. 413). `m` is not assumed piecewise
continuous or continuous. -/
theorem theorem_3_induction_step {c : ℝ → ℝ} {c0 K0 cinf Kinf α : ℝ} {φ m : ℝ → ℝ}
    (hc : IsOrderingCost c) (hc0 : C2Tendsto c (𝓝[>] 0) (c0, K0))
    (hcinf : C2Tendsto c atTop (cinf, Kinf))
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hφ : IsOneSidedPolyaDensity φ)
    (hm_meas : AEMeasurable m) (hm_pf : PFIntegrable m) (hm_bdd : BddBelow (Set.range m))
    (hA1 : AntitoneOn (fun x => (c0 - α * cinf) * x + m x) (Set.Iio 0))
    (hA2 : Tendsto (fun x => (c0 - α * cinf) * x + m x) atBot atTop)
    (hA3 : ∀ a K : ℝ, IsTangentPair c a K →
      NonKDecreasingOn ((1 - α) * K) (fun x => (1 - α) * a * x + m x) (Set.Ici 0))
    (hA4 : Tendsto (fun x => (1 - α) * cinf * x + m x) atTop atTop)
    {F : ℝ → ℝ} (hF1 : PiecewiseContinuous F ∧ PFIntegrable F)
    (hF2 : AntitoneOn (fun x => cinf * x + F x) (Set.Iio 0))
    (hF3 : ∀ a K : ℝ, IsTangentPair c a K → NonKDecreasingOn K (fun x => a * x + F x) Set.univ) :
    (PiecewiseContinuous (valueOp c (conv (fun x => m x + α * F x) φ)) ∧
        PFIntegrable (valueOp c (conv (fun x => m x + α * F x) φ))) ∧
      AntitoneOn (fun x => cinf * x + valueOp c (conv (fun x => m x + α * F x) φ) x)
        (Set.Iio 0) ∧
      ∀ a K : ℝ, IsTangentPair c a K →
        NonKDecreasingOn K (fun x => a * x + valueOp c (conv (fun x => m x + α * F x) φ) x)
          Set.univ := by sorry

end PorteusGenSS
