-- Prove2me | Theorems.Thm_PorteusGenSS_theorem_3_generalized_sS_optimal
-- name    : PorteusGenSS.theorem_3_generalized_sS_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:21:19.080719+00:00
-- url     : https://prove2.me/theorems/0bf42c63-2eec-4ed6-bcf6-fab66f6e0910
-- title:
--   Theorem 3: a generalized $(s,S)$ policy is optimal in every period
-- statement:
--   Standing assumptions: $c$ is concave and nondecreasing on $[0,\infty)$ with $c(0)=0$, and its tangent parameters converge, $C_2(z)\to(c_0,K_0)$ as $z\downarrow0$ and $C_2(z)\to(c_\infty,K_\infty)$ as $z\to\infty$; $0\le\alpha\le1$; $\varphi$ is a one-sided Pólya density; $m$ is measurable, PF-integrable and bounded below. Assumptions A1–A4:
--
--   - A1. $x\mapsto(c_0-\alpha c_\infty)x+m(x)$ is nonincreasing on $(-\infty,0)$;
--   - A2. $(c_0-\alpha c_\infty)x+m(x)\to\infty$ as $x\to-\infty$;
--   - A3. for every $a\in C$, $x\mapsto(1-\alpha)a x+m(x)$ is non-$(1-\alpha)K_a$-decreasing on $[0,\infty)$;
--   - A4. $(1-\alpha)c_\infty x+m(x)\to\infty$ as $x\to\infty$.
--   - A5. $f_0$ is piecewise continuous and PF-integrable, $x\mapsto c_\infty x+f_0(x)$ is nonincreasing on $(-\infty,0)$, and for every $a\in C$, $x\mapsto ax+f_0(x)$ is non-$K_a$-decreasing on $\mathbb R$.
--
--   Define $f_n(x)=\inf_{y\ge x}\{c(y-x)+h_n(y)\}$ with $h_n=(m+\alpha f_{n-1})*\varphi$ for $n\ge1$, and $Y_n(x)$ the set of minimizers. Then for every period $n\ge1$ there exist $s,S\in\mathbb R$ and a generalized $(s,S)$ policy $y$ such that
--
--   $$
--   y(x)\in Y_n(x)\qquad\text{for every }x\in\mathbb R .
--   $$
--
--   Thus a generalized $(s,S)$ policy is optimal in any finite-horizon problem with a concave increasing ordering cost, extending Scarf's $(s,S)$ theorem beyond setup-plus-linear costs. No continuity or piecewise continuity of $m$ is assumed.
--
--   Differences from the source:
--
--   - encoding: periods n ≥ 1 → n : ℕ with hFn … n = h_{n+1}; reason: index shift only; ∀ n : ℕ covers every period ≥ 1
--   - reading: optimal in any finite horizon problem → ∀ n, ∃ s S y, IsGenSSPolicy s S y ∧ ∀ x, y x ∈ Yset c (hFn … n) x; reason: fn and hn do not depend on the horizon N, so every horizon is every period n ≥ 1; s, S, y may depend on n as in the proof
--   - encoding: hn = L + αfn−1∗φ → conv (fun x => m x + α * F x) φ; reason: the second form (m + αfn−1)∗φ of (3), as printed
--   - encoding: fn(x) = inf_{y≥x}{c(y − x) + hn(y)} → valueOp: real ⨅ over Set.Ici x; reason: under the hypotheses the infimum is attained (Lemma 3), so the default value 0 is never reached
--   - encoding: for c ∈ C … K_c → ∀ a K, IsTangentPair c a K → …; reason: K_c is unique for its slope; same instances
--   - encoding: lim_{z↓0} C2(z) = (c0, K0), lim_{z→∞} C2(z) = (c∞, K∞) → C2Tendsto c (𝓝[>] 0) (c0, K0), C2Tendsto c atTop (cinf, Kinf) (set convergence); reason: C2(z) is a singleton for z > 0; same as the ordinary limit
--   - reading: c concave increasing → ConcaveOn and MonotoneOn on [0, ∞) (nondecreasing); reason: the paper never defines "increasing"; nondecreasing is the weaker hypothesis, so the theorem covers every strictly increasing c as well
--   - encoding: convolution integral ∫ f(y − ξ)g(ξ) dξ → Bochner integral conv (0 if not integrable); reason: the integrands here are integrable by PF-integrability, so the default is never reached
--   - encoding: m (Lebesgue) measurable (§X) → AEMeasurable m (for the Lebesgue measure volume); reason: a real function is Lebesgue measurable iff it agrees a.e. with a Borel function; same functions
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), Theorem 3, p. 419

import Mathlib
import Definitions.Def_PorteusGenSS_IsOrderingCost
import Definitions.Def_PorteusGenSS_C2Tendsto
import Definitions.Def_PorteusGenSS_IsTangentPair
import Definitions.Def_PorteusGenSS_IsOneSidedPolyaDensity
import Definitions.Def_PorteusGenSS_PFIntegrable
import Definitions.Def_PorteusGenSS_PiecewiseContinuous
import Definitions.Def_PorteusGenSS_NonKDecreasingOn
import Definitions.Def_PorteusGenSS_IsGenSSPolicy
import Definitions.Def_PorteusGenSS_Yset
import Definitions.Def_PorteusGenSS_hFn

open Filter Topology

namespace PorteusGenSS

/-- **Theorem 3 (a generalized (s, S) policy is optimal in every period).**
Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), Theorem 3, p. 419:
"If A1–A5 hold, then a generalized (s, S) policy is optimal in any finite horizon problem."

Under the standing assumptions of §II (p. 412: `c` concave increasing with `c(0) = 0`, the limits
`(c₀, K₀)` of `C₂(z)` as `z ↓ 0` and `(c_∞, K_∞)` as `z → ∞`), §III (p. 413: `0 ≤ α ≤ 1`, `φ` a
one-sided Pólya density, `m` PF-integrable and bounded below) and §X (p. 425: `m` (Lebesgue) measurable, i.e. `AEMeasurable m` for the Lebesgue measure), and assumptions A1–A5 (§VI, p. 417), for every period `n ≥ 1` there are real
`s, S` and a generalized `(s, S)` policy `y` (Definition 4) such that `y(x) ∈ Yₙ(x)` for every
inventory level `x`, where `Yₙ(x)` is the set of minimizers over `y ≥ x` of
`c(y − x) + hₙ(y)` and `hₙ = (m + αf_{n−1})∗φ`.

**Formalization Note.** The Lean index `n : ℕ` is the paper's period `n + 1`: `hFn … n` is
`h_{n+1}`, so `∀ n : ℕ` covers every period `≥ 1`. Since `fₙ`, `hₙ` do not depend on the
horizon `N`, "any finite horizon problem" is "every period `n ≥ 1`". `c ∈ C` with its `K_c` is
`∀ a K, IsTangentPair c a K → …`. `m` is **not** assumed piecewise continuous or continuous
(the paper never assumes it); `f₀`'s measurability follows from its piecewise continuity (A5). -/
theorem theorem_3_generalized_sS_optimal {c : ℝ → ℝ} {c0 K0 cinf Kinf α : ℝ} {φ m : ℝ → ℝ}
    (hc : IsOrderingCost c) (hc0 : C2Tendsto c (𝓝[>] 0) (c0, K0))
    (hcinf : C2Tendsto c atTop (cinf, Kinf))
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hφ : IsOneSidedPolyaDensity φ)
    (hm_meas : AEMeasurable m) (hm_pf : PFIntegrable m) (hm_bdd : BddBelow (Set.range m))
    (hA1 : AntitoneOn (fun x => (c0 - α * cinf) * x + m x) (Set.Iio 0))
    (hA2 : Tendsto (fun x => (c0 - α * cinf) * x + m x) atBot atTop)
    (hA3 : ∀ a K : ℝ, IsTangentPair c a K →
      NonKDecreasingOn ((1 - α) * K) (fun x => (1 - α) * a * x + m x) (Set.Ici 0))
    (hA4 : Tendsto (fun x => (1 - α) * cinf * x + m x) atTop atTop)
    {f0 : ℝ → ℝ}
    (hA5 : PiecewiseContinuous f0 ∧ PFIntegrable f0 ∧
      AntitoneOn (fun x => cinf * x + f0 x) (Set.Iio 0) ∧
      ∀ a K : ℝ, IsTangentPair c a K → NonKDecreasingOn K (fun x => a * x + f0 x) Set.univ) :
    ∀ n : ℕ, ∃ s S : ℝ, ∃ y : ℝ → ℝ,
      IsGenSSPolicy s S y ∧ ∀ x : ℝ, y x ∈ Yset c (hFn c α φ m f0 n) x := by sorry

end PorteusGenSS
