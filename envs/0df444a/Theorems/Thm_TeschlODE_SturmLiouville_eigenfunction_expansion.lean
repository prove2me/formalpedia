-- Prove2me | Theorems.Thm_TeschlODE_SturmLiouville_eigenfunction_expansion
-- name    : TeschlODE.SturmLiouville.eigenfunction_expansion
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T11:42:05.106617+00:00
-- url     : https://prove2.me/theorems/d46bcd5b-fe6c-4a43-a3c2-b60e77c3dd40
-- title:
--   Theorem 5.11 — eigenvalues and eigenfunction expansion of the regular Sturm–Liouville problem
-- statement:
--   Assume (5.45): $a < b$, $r, q \in C([a,b],\mathbb{R})$, $p \in C^1([a,b],\mathbb{R})$, $p, r > 0$ on $[a,b]$, and fix $\alpha, \beta \in \mathbb{R}$. Let $L = r^{-1}\bigl(-\frac{d}{dx} p \frac{d}{dx} + q\bigr)$ on $D(L) = \{f \in C^2([a,b],\mathbb{C}) : BC_a(f) = BC_b(f) = 0\}$ and $H_0 = C([a,b],\mathbb{C})$ with $\langle f, g\rangle = \int_a^b f^* g\, r\, dx$.
--
--   Then the regular Sturm–Liouville problem has a countable number of discrete and simple eigenvalues $E_n$ which accumulate only at $\infty$, and the corresponding normalized eigenfunctions $u_n$ can be chosen real-valued and form an orthonormal basis of $H_0$:
--   $$f(x) = \sum_{n=0}^{\infty} \langle u_n, f\rangle\, u_n(x), \qquad f \in H_0, \qquad (5.70)$$
--   with convergence in $H_0$; for $f \in D(L)$ the series converges uniformly on $[a,b]$.
--
--   Precisely: there are $E : \mathbb{N} \to \mathbb{R}$ and real-valued $u_n$ such that
--   - each $u_n$ is an eigenfunction of $L$ for $E_n$, and the $E_n$ are pairwise distinct;
--   - every eigenvalue $z \in \mathbb{C}$ of $L$ equals some $E_n$, and every eigenfunction for it is a constant multiple of $u_n$ on $[a,b]$ (simplicity);
--   - $|E_n| \to \infty$ (no finite accumulation point);
--   - $\langle u_m, u_n\rangle = \delta_{mn}$;
--   - for every $f \in H_0$, $\bigl\| f - \sum_{n<N} \langle u_n, f\rangle u_n \bigr\| \to 0$ as $N \to \infty$;
--   - for every $f \in D(L)$, $\sum_{n<N} \langle u_n, f\rangle u_n \to f$ uniformly on $[a,b]$.
--
--   This is the eigenfunction expansion theorem for regular Sturm–Liouville problems, the basis of separation of variables for the heat and wave equations on an interval (§5.1).
--
--   **Formalization Note.** "Countable, discrete, accumulating only at $\infty$" is read as: the eigenvalues are exactly the values of an injective sequence $E_n$ with $|E_n| \to \infty$ (so there are infinitely many, and only finitely many in any bounded set). "Simple" is: every eigenfunction for $E_n$ is $c\,u_n$ on $[a,b]$. "Can be chosen real-valued" is the existential choice of $u_n : \mathbb{R} \to \mathbb{R}$. The orthonormal basis is the book's (5.32)/(5.34) in the incomplete space $H_0$: norm convergence of the partial sums, written as $\operatorname{Re}\langle f - S_N f, f - S_N f\rangle \to 0$, not Mathlib's `HilbertBasis` and not $L^2$. The sequence $E_n$ is not required to be increasing here (the ordering is Lemma 5.12). $\alpha, \beta$ are arbitrary reals; the boundary conditions depend only on them modulo $\pi$.
-- source:
--   Teschl, Ordinary Differential Equations and Dynamical Systems (author's preliminary version of AMS GSM 140, 2012), p. 160, Theorem 5.11

import Mathlib
import Definitions.Def_TeschlODE_SturmLiouville_RegularSL
import Definitions.Def_TeschlODE_SturmLiouville_SLOp
import Definitions.Def_TeschlODE_SturmLiouville_SLDomain
import Definitions.Def_TeschlODE_SturmLiouville_IsSLEigenfunction
import Definitions.Def_TeschlODE_SturmLiouville_SLInner

namespace TeschlODE.SturmLiouville

/-- Teschl, Theorem 5.11, p. 160: under (5.45), the regular Sturm–Liouville problem
`L = r⁻¹(−(d/dx) p (d/dx) + q)` on `D(L)` (5.53)–(5.55) has countably many discrete, simple
eigenvalues `Eₙ` accumulating only at `∞`: there are real `Eₙ` (pairwise distinct, `|Eₙ| → ∞`)
and real-valued eigenfunctions `uₙ ∈ D(L)`, `L uₙ = Eₙ uₙ`, such that every eigenvalue `z ∈ ℂ` of
`L` is some `Eₙ` and every eigenfunction for it is a multiple of `uₙ`. The `uₙ` are orthonormal
for (5.52) and form an orthonormal basis of `H₀ = C([a, b], ℂ)`: for every `f ∈ H₀` the partial
sums of `Σ ⟨uₙ, f⟩ uₙ` (5.70) converge to `f` in the `H₀`-norm; for `f ∈ D(L)` they converge
uniformly on `[a, b]`. -/
theorem eigenfunction_expansion {p q r : ℝ → ℝ} {a b : ℝ} (α β : ℝ)
    (hreg : RegularSL p q r a b) :
    ∃ (E : ℕ → ℝ) (u : ℕ → ℝ → ℝ),
      (∀ n, IsSLEigenfunction p q r a b α β (E n : ℂ) (fun x => ((u n x : ℝ) : ℂ))) ∧
      Function.Injective E ∧
      (∀ (z : ℂ) (f : ℝ → ℂ), IsSLEigenfunction p q r a b α β z f →
        ∃ n, z = (E n : ℂ) ∧ ∃ c : ℂ, ∀ x ∈ Set.Icc a b, f x = c * (u n x : ℂ)) ∧
      Filter.Tendsto (fun n => |E n|) Filter.atTop Filter.atTop ∧
      (∀ m n, SLInner r a b (fun x => ((u m x : ℝ) : ℂ)) (fun x => ((u n x : ℝ) : ℂ)) =
        if m = n then 1 else 0) ∧
      (∀ f : ℝ → ℂ, ContinuousOn f (Set.Icc a b) →
        Filter.Tendsto
          (fun N => (SLInner r a b
            (f - fun x => ∑ n ∈ Finset.range N,
              SLInner r a b (fun y => ((u n y : ℝ) : ℂ)) f * (u n x : ℂ))
            (f - fun x => ∑ n ∈ Finset.range N,
              SLInner r a b (fun y => ((u n y : ℝ) : ℂ)) f * (u n x : ℂ))).re)
          Filter.atTop (nhds 0)) ∧
      (∀ f : ℝ → ℂ, SLDomain p a b α β f →
        TendstoUniformlyOn
          (fun N x => ∑ n ∈ Finset.range N,
            SLInner r a b (fun y => ((u n y : ℝ) : ℂ)) f * (u n x : ℂ))
          f Filter.atTop (Set.Icc a b)) := by sorry

end TeschlODE.SturmLiouville
