-- Prove2me | Theorems.Thm_Roberts1997_RWM_discGen_uniform_convergence
-- name    : Roberts1997.RWM.discGen_uniform_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T15:49:05.367781+00:00
-- url     : https://prove2.me/theorems/9ece9138-2106-43e7-8505-5f70c72b946c
-- title:
--   Lemma 2.6 — uniform convergence of the discrete generator G_n to the Langevin generator G on F_n (with the proof's bounded (log f)‴)
-- statement:
--   Let $f$ satisfy the standing hypotheses, and in addition let $f\in C^3$ with $\sup_{z\in\mathbb R}|(\log f)'''(z)|<\infty$ (the assumption used by the paper's proof; see the Formalization Note). Let $l>0$. Let $v\in C_c^\infty(\mathbb R)$ and let $V(x)=v(x_1)$ be the function of the first component of $x\in\mathbb R^n$ that it defines. Then
--
--   $$ \sup_{x\in F_n}\big|G_nV(x)-Gv(x_1)\big|\longrightarrow0\qquad(n\to\infty), $$
--
--   where $G_nV(x)=n\,\mathbb E\big[(V(Y)-V(x))(1\wedge\pi_n(Y)/\pi_n(x))\big]$ with $Y\sim N(x,\frac{l^2}{n-1}I_n)$ and $Gv(x_1)=h(l)\big[\frac12v''(x_1)+\frac12(\log f)'(x_1)v'(x_1)\big]$. Equivalently, for every $\varepsilon>0$, for all large $n$ and all $x\in F_n$, $|G_nV(x)-Gv(x_1)|\le\varepsilon$.
--
--   This is the key estimate of the paper: on the sets $F_n$, where the chain stays with probability tending to one (Lemma 2.1), the generator of the speeded-up chain acting on functions of the first coordinate converges uniformly to the generator of the Langevin diffusion.
--
--   **Formalization Note** The page prints "as $d\to\infty$"; the paper has no $d$, and this is read as $n\to\infty$. "$V\in C_c^\infty$ is a function of the first component" is read as $V(x)=v(x_1)$ with $v$ smooth and compactly supported on $\mathbb R$. The supremum is over all of $F_n$ (no restriction on $x_1$) and is stated as eventual uniform smallness. **Added hypothesis (correction of a gap of the page).** The page states the lemma under the paper's standing hypotheses ($f\in C^2$ positive, $(\log f)'$ Lipschitz, (A1), (A2)), but its proof (p. 116) bounds the Taylor remainder by $\sup_{z\in\mathbb R}|(\log f)'''(z)|$. Under $C^2$ alone the uniformity over $F_n$ fails: if $(\log f)''$ has narrow spikes of fixed height at points tending to infinity, a positive fraction of the coordinates $x_2,\dots,x_n$ can be placed on spikes of width $\ll n^{-1/2}$ while $R_n,S_n$ stay within $n^{-1/8}$ of $I$; the Taylor remainder then shifts the mean of the log acceptance ratio by a non-vanishing constant and $G_nV(x)\not\to Gv(x_1)$ on those $x$. The statement therefore carries $f\in C^3$ and bounded $(\log f)'''$, which is the proof's own assumption. Theorem 1.1 itself keeps the paper's hypotheses.
-- source:
--   Roberts, Gelman, Gilks, Weak convergence and optimal scaling of random walk Metropolis algorithms, Ann. Appl. Probab. 7(1), 1997, p. 116, Lemma 2.6

import Definitions.Def_Roberts1997_RWM_IsRegularTarget
import Definitions.Def_Roberts1997_RWM_ProofObjects
import Definitions.Def_Roberts1997_RWM_Langevin

open MeasureTheory ProbabilityTheory Filter
open scoped ContDiff

namespace Roberts1997.RWM

/-- Lemma 2.6 (p. 116). For `V ∈ C_c^∞` depending on the first component only,
`V(x) = v(x₁)`, `sup_{x ∈ F_n} |G_n V(x) - G v(x₁)| → 0` as `n → ∞` (the page's
"as d → ∞" is a misprint for `n → ∞`); stated as eventual uniform smallness.
Correction of a gap of the page: the printed proof (p. 116) uses `sup_{z ∈ ℝ} |(log f)'''(z)|`,
which the paper's hypotheses (`f ∈ C²`) do not supply, and under `C²` alone the uniformity over
`F_n` fails; the hypotheses `hf3` (`f ∈ C³`) and `hK` (`(log f)'''` bounded) are that
assumption of the proof, added. -/
theorem discGen_uniform_convergence (f : ℝ → ℝ) (hf : IsRegularTarget f)
    (hf3 : ContDiff ℝ 3 f)
    (hK : ∃ K : ℝ, ∀ z : ℝ, |iteratedDeriv 3 (fun y => Real.log (f y)) z| ≤ K)
    (l : ℝ) (hl : 0 < l)
    (v : ℝ → ℝ) (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ x ∈ Fn f n,
      |discGen f n l (fun y => v (first y)) x - langevinGen f l v (first x)| ≤ ε := by sorry

end Roberts1997.RWM
