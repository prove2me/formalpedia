-- Prove2me | Theorems.Thm_PorteusGenSS_lemma_3_G_in_CK
-- name    : PorteusGenSS.lemma_3_G_in_CK
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:19:20.090799+00:00
-- url     : https://prove2.me/theorems/81a6d12e-4041-488c-a1ed-ffee4f5cba53
-- title:
--   Lemma 3: $G_{cn}\in C(K_c)$, nonincreasing on $\mathbb R^-$, and $Y_n(x)\neq\emptyset$
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
--   Put $h=(m+\alpha F)*\varphi$ (the paper's $h_n$). Then
--
--   1. for every $a\in C$, the function $G_{an}(x)=ax+h(x)$ belongs to $C(K_a)$ and is nonincreasing on $(-\infty,0)$;
--   2. for every $x\in\mathbb R$ the set $Y_n(x)$ of minimizers of $y\mapsto c(y-x)+h(y)$ over $y\ge x$ is nonempty.
--
--   No continuity or piecewise continuity of $m$ is assumed.
--
--   Differences from the source:
--
--   - encoding: Gcn = gcn∗φ with gcn = c· + m + αfn−1 + cμ ((5), (6)) → fun x => a * x + h x; reason: the paper's identity (7), Gcn = c· + hn; same function
--   - encoding: hn = L + αfn−1∗φ → conv (fun x => m x + α * F x) φ; reason: the second form (m + αfn−1)∗φ of (3), as printed
--   - encoding: for c ∈ C … K_c → ∀ a K, IsTangentPair c a K → …; reason: K_c is unique for its slope; same instances
--   - encoding: lim_{z↓0} C2(z) = (c0, K0), lim_{z→∞} C2(z) = (c∞, K∞) → C2Tendsto c (𝓝[>] 0) (c0, K0), C2Tendsto c atTop (cinf, Kinf) (set convergence); reason: C2(z) is a singleton for z > 0; same as the ordinary limit
--   - reading: c concave increasing → ConcaveOn and MonotoneOn on [0, ∞) (nondecreasing); reason: the paper never defines "increasing"; nondecreasing is the weaker hypothesis, so the theorem covers every strictly increasing c as well
--   - encoding: convolution integral ∫ f(y − ξ)g(ξ) dξ → Bochner integral conv (0 if not integrable); reason: the integrands here are integrable by PF-integrability, so the default is never reached
--   - encoding: m (Lebesgue) measurable (§X) → AEMeasurable m (for the Lebesgue measure volume); reason: a real function is Lebesgue measurable iff it agrees a.e. with a Borel function; same functions
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), Lemma 3, p. 418 (proof pp. 418–419)

import Mathlib
import Definitions.Def_PorteusGenSS_IsOrderingCost
import Definitions.Def_PorteusGenSS_C2Tendsto
import Definitions.Def_PorteusGenSS_IsTangentPair
import Definitions.Def_PorteusGenSS_IsOneSidedPolyaDensity
import Definitions.Def_PorteusGenSS_PFIntegrable
import Definitions.Def_PorteusGenSS_PiecewiseContinuous
import Definitions.Def_PorteusGenSS_NonKDecreasingOn
import Definitions.Def_PorteusGenSS_InCK
import Definitions.Def_PorteusGenSS_conv
import Definitions.Def_PorteusGenSS_Yset

open Filter Topology

namespace PorteusGenSS

/-- **Lemma 3 (G_cn ∈ C(K_c), nonincreasing on R⁻, and Yₙ(x) ≠ ∅).**
Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), Lemma 3, p. 418 (proof pp. 418–419):
"If, for a given n ≥ 1, (i) fn−1 is piecewise continuous and PF-integrable, (ii) c∞· + fn−1 is
nonincreasing on R−, (iii) c· + fn−1 is non-Kc-decreasing on R for c ∈ C, and A1–A4 hold, then
Gcn ∈ C(Kc) and is nonincreasing on R− for c ∈ C, and Yn(x) is nonempty for each x ∈ R."

Under the standing assumptions of §II (p. 412: `c` concave increasing with `c(0) = 0`, the limits
`(c₀, K₀)` of `C₂(z)` as `z ↓ 0` and `(c_∞, K_∞)` as `z → ∞`), §III (p. 413: `0 ≤ α ≤ 1`, `φ` a
one-sided Pólya density, `m` PF-integrable and bounded below) and §X (p. 425: `m` (Lebesgue) measurable, i.e. `AEMeasurable m` for the Lebesgue measure), assumptions A1–A4 (§VI, p. 417), and (i)–(iii) for a function `F` (the paper's
`f_{n−1}`), let `h = (m + αF)∗φ` (the paper's `hₙ`). Then for every `c ∈ C` with intercept `K_c`
the function `G_cn = c· + h` belongs to `C(K_c)` and is nonincreasing on `(−∞, 0)`, and the set
`Yₙ(x)` of optimal order-up-to levels is nonempty for every `x`.

**Formalization Note.** `G_cn` is written as `c· + hₙ`, the paper's identity (7), p. 413;
`hₙ = (m + αf_{n−1})∗φ` is the second form of (3). `c ∈ C` with `K_c` is
`∀ a K, IsTangentPair c a K → …`. R⁻ is `Set.Iio 0`. `m` is **not** assumed piecewise continuous
or continuous: the paper's hypotheses on `m` are measurability, PF-integrability, boundedness
below and A1–A4. -/
theorem lemma_3_G_in_CK {c : ℝ → ℝ} {c0 K0 cinf Kinf α : ℝ} {φ m : ℝ → ℝ}
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
    (∀ a K : ℝ, IsTangentPair c a K →
        InCK K (fun x => a * x + conv (fun x => m x + α * F x) φ x) ∧
        AntitoneOn (fun x => a * x + conv (fun x => m x + α * F x) φ x) (Set.Iio 0)) ∧
      ∀ x : ℝ, (Yset c (conv (fun x => m x + α * F x) φ) x).Nonempty := by sorry

end PorteusGenSS
