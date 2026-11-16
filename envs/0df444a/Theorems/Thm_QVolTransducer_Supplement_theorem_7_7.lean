-- Prove2me | Theorems.Thm_QVolTransducer_Supplement_theorem_7_7
-- name    : QVolTransducer.Supplement.theorem_7_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:42:53.477755+00:00
-- url     : https://prove2.me/theorems/bf533fcb-71f9-490c-a68e-b9012165cf60
-- title:
--   Theorem 7.7 — naive grid discretization of a Metropolis walk: reversibility and uniform convergence of stationary distributions
-- statement:
--   Let $\Omega\subseteq\mathbb R^d$ be Jordan-measurable, $0<a<b$, $L>0$, $h(\zeta)\downarrow0$ as $\zeta\downarrow0$, and for every $x\in\Omega$ let $p_x:\Omega\to\{0\}\cup[a,b]$ be piecewise $L$-Lipschitz on an $h$-smooth partition $(\Omega_j^{(x)})_{j=1}^n$, not identically zero, with $p_x(y)=p_y(x)$ for all $x,y\in\Omega$. Suppose $\ell(x):=N_{p_x}=\int_\Omega p_x$ and $f$ take values in $[a,b]$ and are piecewise $L$-Lipschitz on an $h$-smooth partition. Let $(\Omega,P)$ be the Metropolis process with proposal distributions $(p_x)$ and density $f$, and $(\Omega_\zeta,P_\zeta)$ its naive discretization. Then
--
--   1. $(\Omega,P)$ is reversible with respect to $\pi_{f\cdot\ell}$, and for every $\zeta>0$, $(\Omega_\zeta,P_\zeta)$ is reversible with respect to $\pi_{f\cdot\bar\ell,\zeta}$, where $\bar\ell(x)=N_{(p_x)_\zeta}$;
--   2. $f\cdot\ell$, and hence $\pi_{f\cdot\ell}$, is piecewise Lipschitz and globally bounded on an $h$-smooth partition;
--   3. there is a function $G(a,b,L,h,V;\zeta)\to0$ as $\zeta\downarrow0$ (for fixed $d$) such that for every $\zeta>0$
--   $$\sup_{x\in\Omega_\zeta}\Big|\frac{\pi_{f\cdot\bar\ell,\zeta}(x)}{\zeta^d}-\pi_{f\cdot\ell}(x)\Big|\le G(a,b,L,h,\mathrm{Vol}(\Omega);\zeta),$$
--   i.e. the supremum tends to $0$ at a rate depending only on $a,b,L,h$ and $\mathrm{Vol}(\Omega)$.
--
--   For smooth enough walks the naive grid discretization therefore perturbs the stationary distribution by a vanishing amount, uniformly over all walks with the same parameters.
--
--   **Formalization Note** The process is a map from points to measures; "the Markov process" includes that $x\mapsto P(x,B)$ is measurable for Borel $B$ (Definition 6.1). Reversibility of $P_\zeta$ is detailed balance between distinct grid points. "Globally bounded" means values in $[a',b']$ with $0<a'<b'$.
--
--   Differences from the source:
--   - reading: ℓ and f piecewise L-Lipschitz 'on an h-smooth partition too' → one h-smooth partition shared by ℓ and f, with the same L and h; each p_x has its own partition with the same n; reason: the singular 'an h-smooth partition'; the conclusion for f·ℓ uses a common partition
--   - reading: '(Ω, P) the Markov process' → x ↦ P(x, B) is measurable for every Borel B; reason: a Markov process is given by a Markov kernel (Definition 6.1, condition 1)
--   - reading: '↓ 0 (ζ ↓ 0), where the rate of convergence can be upper bounded depending only on a, b, L, h and Vol(Ω)' → ∃ G (for each d) with G(a, b, L, h, V; ζ) → 0 as ζ → 0⁺ bounding the supremum for every ζ > 0 and every admissible (Ω, p, f) with Vol(Ω) = V; reason: a rate depending only on the listed quantities is a common bound G; the dimension d is fixed
--   - encoding: (Ω_ζ, P_ζ) reversible w.r.t. π_{f·ℓ̄,ζ} → detailed balance π(x)P_ζ(x, y) = π(y)P_ζ(y, x) for distinct grid points x, y of Ω; reason: the diagonal does not enter detailed balance; where N_{(p_x)_ζ} = 0 the row is the identity
--   - encoding: globally bounded → values in [a′, b′] with 0 < a′ < b′ on Ω; reason: the meaning of Lemma 7.3
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Theorem 7.7, p.45 (PDF p.47)

import Mathlib
import Definitions.Def_QVolTransducer_gridIdx
import Definitions.Def_QVolTransducer_IsPiecewiseLipschitz
import Definitions.Def_QVolTransducer_Supplement_measCond
import Definitions.Def_QVolTransducer_Supplement_metroKernel

namespace QVolTransducer.Supplement

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **Naive grid discretization of a Metropolis walk** (Cornelissen, Apers, Gribling, *Improved
quantum volume estimation with transducers and amortized quantum walks*, arXiv:2609.40217 (version
of November 3, 2026, sha256 40d7b52d…), Theorem 7.7, p.45 (PDF p.47)).

For every dimension `d` there is a function `G(a, b, L, h, V; ζ)` with `G(a, b, L, h, V; ζ) → 0` as
`ζ ↓ 0` (for all `a, b, L, h, V`) with the following property. Let `Ω ⊆ ℝ^d` be Jordan-measurable,
`0 < a < b`, `L > 0`, `h(ζ) ↓ 0` as `ζ ↓ 0`, and for all `x ∈ Ω` let `p_x : Ω → {0} ∪ [a, b]` be
piecewise `L`-Lipschitz on an `h`-smooth partition `(Ω_j^(x))_{j=1}^n`, not identically `0`, with
`p_x(y) = p_y(x)` for all `x, y ∈ Ω`. Suppose `ℓ(x) := N_{p_x} = ∫_Ω p_x` and `f` take values in
`[a, b]` on `Ω` and are piecewise `L`-Lipschitz on an `h`-smooth partition (one partition for
both). Let `(Ω, P)` be the Markov process with proposal distributions `(p_x)` and density `f`, and
`(Ω_ζ, P_ζ)` its naive discretization. Then
1. `(Ω, P)` is reversible with respect to `π_{f·ℓ}`;
2. for every `ζ > 0`, `(Ω_ζ, P_ζ)` is reversible with respect to `π_{f·ℓ̄,ζ}`, `ℓ̄(x) = N_{(p_x)_ζ}`;
3. `f·ℓ` is piecewise Lipschitz and globally bounded on an `h`-smooth partition, and so is
   `π_{f·ℓ}`;
4. for every `ζ > 0`, `sup_{x∈Ω_ζ} |π_{f·ℓ̄,ζ}(x)/ζ^d − π_{f·ℓ}(x)| ≤ G(a, b, L, h, Vol(Ω); ζ)`,
   i.e. the supremum tends to `0` as `ζ ↓ 0` at a rate depending only on `a, b, L, h, Vol(Ω)`.

**Formalization Note** `p x y` is `p_x(y)`; `P` is the published-style transition law
`metroKernel` (Definition 7.6) and `P_ζ` has the off-diagonal entries `metroGrid` (the diagonal does
not enter detailed balance). "The Markov process" is read as including that `P` is a Markov kernel
(Definition 6.1): `x ↦ P(x, B)` is measurable for every Borel `B`. Reversibility of `P` is
Definition 6.4 for Borel sets of `ℝ^d` (`π_{f·ℓ}` is concentrated on `Ω`); reversibility of `P_ζ`
is detailed balance between distinct grid points of `Ω`. "Globally bounded" means values in
`[a′, b′]` with `0 < a′ < b′` (Lemma 7.3). The rate is a single function `G` of
`(a, b, L, h, Vol(Ω), ζ)` (for fixed `d`), not depending on `n`, `Ω`, `p` or `f` otherwise. At a
`ζ` with `N_{(p_x)_ζ} = 0` the row of `P_ζ` is the identity (Lean's `x/0 = 0`). -/
theorem theorem_7_7 (d : ℕ) :
    ∃ G : ℝ → ℝ → ℝ → (ℝ → ℝ) → ℝ → ℝ → ℝ,
      (∀ a b L (h : ℝ → ℝ) V, Tendsto (G a b L h V) (𝓝[>] 0) (𝓝 0)) ∧
      ∀ (Ω : Set (EuclideanSpace ℝ (Fin d))) (a b L : ℝ) (h : ℝ → ℝ) (n m : ℕ)
        (p : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ)
        (partsP : EuclideanSpace ℝ (Fin d) → Fin n → Set (EuclideanSpace ℝ (Fin d)))
        (f : EuclideanSpace ℝ (Fin d) → ℝ) (parts : Fin m → Set (EuclideanSpace ℝ (Fin d))),
        IsJordanMeasurable Ω → 0 < a → a < b → 0 < L →
        (∀ x ∈ Ω, ∀ y ∈ Ω, p x y = 0 ∨ p x y ∈ Set.Icc a b) →
        (∀ x ∈ Ω, IsPiecewiseLipschitz (p x) Ω L (partsP x) h) →
        (∀ x ∈ Ω, ∃ y ∈ Ω, p x y ≠ 0) →
        (∀ x ∈ Ω, ∀ y ∈ Ω, p x y = p y x) →
        (∀ x ∈ Ω, massN Ω (p x) ∈ Set.Icc a b) →
        (∀ x ∈ Ω, f x ∈ Set.Icc a b) →
        IsPiecewiseLipschitz (fun x => massN Ω (p x)) Ω L parts h →
        IsPiecewiseLipschitz f Ω L parts h →
        (∀ B : Set (EuclideanSpace ℝ (Fin d)), MeasurableSet B →
          Measurable fun x => metroKernel Ω p f x B) →
        IsReversibleWrt (metroKernel Ω p f) (metroStat Ω (fun x => f x * massN Ω (p x))) ∧
        (∀ ζ : ℝ, 0 < ζ → ∀ z w : Fin d → ℤ, latticePt ζ z ∈ Ω → latticePt ζ w ∈ Ω → z ≠ w →
          gridDist Ω ζ (fun x => f x * gridSum Ω ζ (p x)) z * metroGrid Ω p f ζ z w =
            gridDist Ω ζ (fun x => f x * gridSum Ω ζ (p x)) w * metroGrid Ω p f ζ w z) ∧
        (∃ L' a' b' : ℝ, 0 < a' ∧ a' < b' ∧
          IsPiecewiseLipschitz (fun x => f x * massN Ω (p x)) Ω L' parts h ∧
          ∀ x ∈ Ω, f x * massN Ω (p x) ∈ Set.Icc a' b') ∧
        (∃ L' a' b' : ℝ, 0 < a' ∧ a' < b' ∧
          IsPiecewiseLipschitz
            (fun x => f x * massN Ω (p x) / massN Ω (fun y => f y * massN Ω (p y))) Ω L' parts h ∧
          ∀ x ∈ Ω, f x * massN Ω (p x) / massN Ω (fun y => f y * massN Ω (p y)) ∈
            Set.Icc a' b') ∧
        ∀ ζ : ℝ, 0 < ζ → ∀ z : Fin d → ℤ, latticePt ζ z ∈ Ω →
          |gridDist Ω ζ (fun x => f x * gridSum Ω ζ (p x)) z / ζ ^ d -
              f (latticePt ζ z) * massN Ω (p (latticePt ζ z)) /
                massN Ω (fun y => f y * massN Ω (p y))| ≤
            G a b L h (volume Ω).toReal ζ := by sorry

end QVolTransducer.Supplement
