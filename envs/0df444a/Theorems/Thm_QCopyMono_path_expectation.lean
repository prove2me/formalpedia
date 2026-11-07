-- Prove2me | Theorems.Thm_QCopyMono_path_expectation
-- name    : QCopyMono.path_expectation
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:46:06.786197+00:00
-- url     : https://prove2.me/theorems/9822891f-a97c-4508-91dd-245c7823ff07
-- title:
--   Eqs. (16)–(19) — $\tfrac12\mathbb E[U_d]-\tfrac14\mathbb E[V_d]=p_{t_d}(f)$
-- statement:
--   Fix an integer $t=t_d\ge1$ and let $\kappa_d$, $Q_d$, $h_d$, $H_d$, $q_d$ be as in §3.2.2. For every $f:\{0,1\}^n\to\{0,1\}$:
--
--   1. $p_{t_d}(f)=\frac1{2^n}\sum_{x,y}\kappa_d(x,y)f(x)(1-f(y))$ (eq. (16));
--   2. $|\langle\xi_{xy}|\psi_f\rangle|^2=\mathbf 1[f(x)\neq f(y)]/2^n$ for $(x,y)\in\mathcal P_d$;
--   3. $\langle\psi_f|Q_d|\psi_f\rangle=q_d(f)$ (eq. (19));
--   4. $\sum_x h_d(x)=0$;
--   5. $\langle\psi_f|H_d\otimes Z|\psi_f\rangle=\frac1{2^n}\sum_x h_d(x)(1-2f(x))=-\frac2{2^n}\sum_x h_d(x)f(x)=-\frac2{2^n}\sum_{x,y}\kappa_d(x,y)(f(x)-f(y))$;
--   6. if $U_d$ and $V_d$ are the outcomes of measuring $Q_d$ and $H_d\otimes Z$ on a copy of $|\psi_f\rangle$, then $\tfrac12\mathbb E[U_d]-\tfrac14\mathbb E[V_d]=p_{t_d}(f)$, i.e. $\mathbb E[\hat p_d]=p_{t_d}(f)$.
--
--   These identities show that the two observables give an unbiased estimator of the classical path tester's violation probability.
--
--   Differences from the source:
--   - generalization: the subsection assumes n ≥ n_0, n^{-1/2} ≤ ε ≤ 1/2 and t = t_d → every n, every ε and every integer t ≥ 1; reason: the identities do not use these assumptions; the subsection's case is an instance
--   - encoding: E[U_d], E[V_d] for measurement outcomes → integrals against the outcome law of measuring the observable in an eigenbasis; reason: the standard law of a projective measurement; same quantities
-- source:
--   Naik, Quantum Copy Complexity of Testing Monotonicity and Other Properties, STOC 2027 submission (manuscript sha256 10fb417512cedc538a3dc512c3cd893806335ae8e073ebaf1deeeab8e5dac528), §3.2.2, pp.14–15, eqs. (16), (19), the H_d ⊗ Z display, and E[p̂_d] = p_{t_d}(f)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QCopyMono_IsMonoTester
import Definitions.Def_QCopyMono_PathExperiment
import Definitions.Def_QCopyMono_PathObservables
import Definitions.Def_QCopyMono_ObsLaw

namespace QCopyMono

open QAlgorithms Matrix MeasureTheory

/-- Naik, *Quantum Copy Complexity of Testing Monotonicity and Other Properties*, STOC 2027
submission (manuscript sha256 10fb4175…dac528), §3.2.2, pp.14–15, eqs. (16), (19) and the
`H_d ⊗ Z` chain: for every integer `t ≥ 1` (here `t = t_d`),

1. `p_t(f) = 2^{−n} ∑_{x,y} κ(x, y) f(x)(1 − f(y))` (eq. (16));
2. `|⟨ξ_{xy}|ψ_f⟩|² = 1[f(x) ≠ f(y)]/2ⁿ` for `(x, y) ∈ P_d`;
3. `⟨ψ_f|Q_d|ψ_f⟩ = q_d(f)` (eq. (19));
4. `∑ₓ h_d(x) = 0`;
5. `⟨ψ_f|H_d ⊗ Z|ψ_f⟩ = 2^{−n} ∑ₓ h_d(x)(1 − 2f(x)) = −2·2^{−n} ∑ₓ h_d(x) f(x)
   = −2·2^{−n} ∑_{x,y} κ(x, y)(f(x) − f(y))`;
6. `E[p̂_d] = p_{t_d}(f)`: with `U_d`, `V_d` the outcomes of measuring `Q_d` and `H_d ⊗ Z` on a
   copy of `|ψ_f⟩`, `½ E[U_d] − ¼ E[V_d] = p_{t_d}(f)`.

**Formalization Note.** `f(x)` is read as `1` or `0`. `⟨ψ|A|ψ⟩` is `star ψ ⬝ᵥ (A *ᵥ ψ)`. The
expectations in 6 are integrals against `obsLaw`, the outcome law of measuring the observable
in its eigenbasis. The subsection's standing assumptions `n ≥ n₀`, `n^{−1/2} ≤ ε ≤ 1/2` and
`t = t_d` are not used by these identities and are not imposed. -/
theorem path_expectation (n : ℕ) (ε : ℝ) (t : ℕ) (ht : 1 ≤ t) (f : Qubits n → Bool) :
    pathProb ε t f = (∑ x : Qubits n, ∑ y : Qubits n, kappa ε t x y *
      ((if f x = true then 1 else 0) * (1 - if f y = true then 1 else 0))) / 2 ^ n ∧
    (∀ x y : Qubits n, PathPair ε t x y →
      Complex.normSq (star (xi x y) ⬝ᵥ fnState f) = (if f x ≠ f y then 1 else 0) / 2 ^ n) ∧
    star (fnState f) ⬝ᵥ (pathQ n ε t *ᵥ fnState f) = ((qd ε t f : ℝ) : ℂ) ∧
    ∑ x : Qubits n, hFun ε t x = 0 ∧
    star (fnState f) ⬝ᵥ (pathHZ n ε t *ᵥ fnState f) =
      (((∑ x : Qubits n, hFun ε t x * (1 - 2 * if f x = true then 1 else 0)) / 2 ^ n : ℝ) : ℂ) ∧
    (∑ x : Qubits n, hFun ε t x * (1 - 2 * if f x = true then 1 else 0)) / 2 ^ n =
      -2 * (∑ x : Qubits n, hFun ε t x * (if f x = true then 1 else 0)) / 2 ^ n ∧
    -2 * (∑ x : Qubits n, hFun ε t x * (if f x = true then 1 else 0)) / 2 ^ n =
      -2 * (∑ x : Qubits n, ∑ y : Qubits n, kappa ε t x y *
        ((if f x = true then 1 else 0) - (if f y = true then 1 else 0))) / 2 ^ n ∧
    (∫ u, u ∂(obsLaw (pathQ n ε t) (pathQ_isHermitian n ε t) (fnVec f))) / 2 -
      (∫ v, v ∂(obsLaw (pathHZ n ε t) (pathHZ_isHermitian n ε t) (fnVec f))) / 4 =
        pathProb ε t f := by sorry

end QCopyMono
