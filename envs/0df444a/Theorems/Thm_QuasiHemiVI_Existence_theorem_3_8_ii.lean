-- Prove2me | Theorems.Thm_QuasiHemiVI_Existence_theorem_3_8_ii
-- name    : QuasiHemiVI.Existence.theorem_3_8_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:35:27.185383+00:00
-- url     : https://prove2.me/theorems/6f20127f-9d79-4518-8640-a54f68bb7259
-- title:
--   Theorem 3.8 (ii) — the solution set $\Gamma(f)$ of Problem 1.1 is nonempty, bounded and weakly closed
-- statement:
--   Let $V$ be a real reflexive Banach space, $X$ and $Y$ real Banach spaces, $C\subseteq V$, $K:C\to2^C$, $T:C\to2^{V^*}$, $\varphi:V\times V\to\mathbb R$, $J:X\to\mathbb R$, $h:V\to\mathbb R$, $\gamma\in\mathcal L(V,X)$, $\pi\in\mathcal L(V,Y)$, $f\in Y^*$ and $C_0\subseteq V$. Assume
--
--   1. (HC): $C$ is nonempty, closed and convex;
--   2. (HJ): $J$ is locally Lipschitz; (Hγ), (H0): $\gamma$ and $\pi$ are bounded linear operators;
--   3. (HT): $T$ has nonempty, compact, convex values and is upper semicontinuous on $C$; $T(\cdot)+\gamma^*\partial J(\gamma\,\cdot)$ is $(\varphi,h)$-stably pseudomonotone with respect to $\{\pi^*f\}$; $\limsup_{t\to0^+}h(tu)/t\ge0$ for all $u$, and $h(v)\le\limsup_n h(v_n)$ whenever $v_n\rightharpoonup v$; and $h$ is convex;
--   4. (Hφ): $\varphi(\cdot,u)$ is convex and l.s.c., $\varphi(v,\cdot)$ is concave and u.s.c., $\varphi(v,v)=0$;
--   5. (HK): $K(u)\subseteq C$ is nonempty, closed and convex, with the Mosco-type conditions (i) and (ii);
--   6. (HC0): $C_0$ is bounded, $K(u)\cap C_0\neq\emptyset$ for all $u\in C$, and, if $C$ is unbounded, the coercivity condition (3.2) holds uniformly in $v_0\in C_0$: for every $M$ there is $R$ with $\langle u^*,u-v_0\rangle+\langle\eta,\gamma(u-v_0)\rangle-\varphi(v_0,u)\ge M\|u\|$ for all $v_0\in C_0$, $u\in C$ with $\|u\|\ge R$, $u^*\in T(u)$, $\eta\in\partial J(\gamma u)$;
--   7. $\gamma$ is compact, and $\limsup_n\varphi(v_n,u_n)\le\varphi(v,u)$ whenever $v_n,u_n\in C$, $v_n\to v$, $u_n\rightharpoonup u$, $u,v\in C$ (3.19).
--
--   Then the solution set $\Gamma(f)$ of the generalized nonlinear quasi-hemivariational inequality
--
--   $$
--   u\in C,\ u\in K(u),\ \exists\,u^*\in T(u):\quad\langle u^*,v-u\rangle+\varphi(v,u)+J^0(\gamma u;\gamma(v-u))\ge\langle f,\pi(v-u)\rangle_{Y^*\times Y}\ \ \forall v\in K(u)
--   $$
--
--   is nonempty, bounded, and weakly closed.
--
--   This is the main existence result of the paper; its solution map $f\mapsto\Gamma(f)$ is the state map of the optimal control problem of Section 4.
--
--   **Formalization Note** "Weakly closed" is sequential weak closedness, equivalent to weak closedness for the bounded set $\Gamma(f)$ in the reflexive space $V$. All $\limsup$ and coercivity conditions are stated with explicit $\varepsilon$–$N$ quantifiers (see the definition `Hypotheses`). Relative to the page, $T(u)\neq\emptyset$ is assumed, the pairing in (3.2) is $\langle\eta_u,\gamma(u-v_0)\rangle$, and (3.2) in (HC0) is required uniformly in $v_0\in C_0$. The last repair is needed: the proof (pp. 1260–1261) uses one rate $r$ for test points $v_n\in C_0\cap K(w_n)$ that vary with $n$, and with (3.2) only at each fixed $v_0$ the conclusion fails. Take $V=\ell^2$, $C=V$, $T(u)=\{u\}$, $J=0$, $\gamma=0$, $\pi=\mathrm{id}$, $f=0$, $h=0$, $\varphi(v,u)=\psi(v)-\psi(u)$ with $\psi(v)=\sum_{k\ge2}k^3\max(0,v_k-\tfrac12-\tfrac{v_1}{2k})$ (finite, convex, continuous, $\psi(e_k)=k^3/2$), $a:\mathbb R\to\ell^2$ the continuous unit-norm path with $a(s)=e_2$ for $s\le2$ and $a(s)=\cos\theta\,e_k+\sin\theta\,e_{k+1}$, $\theta=\tfrac\pi2(s-k)$, on $[k,k+1]$, $K(w)=\{a(\langle e_1,w\rangle)+te_1: t\ge0\}$ and $C_0=a(\mathbb R)$. Every printed hypothesis holds, (3.2) holds at each fixed $v_0\in C_0$, and $e_k+ke_1\in\Gamma(0)$ for every $k\ge2$, so $\Gamma(0)$ is unbounded.
-- source:
--   Zeng, Migórski & Khan, Nonlinear Quasi-hemivariational Inequalities: Existence and Optimal Control, SIAM J. Control Optim. 59(2) (2021) 1246–1274, doi:10.1137/19M1282210, p. 1259, Theorem 3.8 (ii)

import Mathlib
import Definitions.Def_QuasiHemiVI_Existence_ClarkeDeriv
import Definitions.Def_QuasiHemiVI_Existence_WeakConv
import Definitions.Def_QuasiHemiVI_Existence_SetValued
import Definitions.Def_QuasiHemiVI_Existence_Hypotheses
import Definitions.Def_QuasiHemiVI_Existence_Problems

namespace QuasiHemiVI.Existence

/-- Theorem 3.8 (ii), p. 1259 (goal): under (HC), (HJ), (Hγ), (H0), (HT) with `h` convex, (Hφ),
(HK), (HC0), `γ` compact and (3.19), the solution set `Γ(f)` of Problem 1.1 is nonempty, bounded
and (sequentially) weakly closed. (HC0) is taken with (3.2) uniform in `v₀ ∈ C₀` (`HC0Unif`), the
form the proof uses on pp. 1260–1261; with (3.2) only at each fixed `v₀ ∈ C₀`, as printed, `Γ(f)`
can be unbounded (`V = ℓ²`, `φ(v, u) = ψ(v) - ψ(u)` with `ψ` convex, continuous and unbounded on
the unit ball). -/
theorem theorem_3_8_ii {V X Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (hV : IsReflexive V)
    (C : Set V) (K : V → Set V) (T : V → Set (V →L[ℝ] ℝ)) (φ : V → V → ℝ) (J : X → ℝ)
    (γ : V →L[ℝ] X) (π : V →L[ℝ] Y) (f : Y →L[ℝ] ℝ) (h : V → ℝ) (C₀ : Set V)
    (hC : HC C) (hJ : LocallyLipschitz J) (hT : HT C T φ J γ π f h)
    (hhcvx : ConvexOn ℝ Set.univ h) (hφ : Hphi φ) (hK : HK C K) (hC0 : HC0Unif C K T φ J γ C₀)
    (hγ : IsCompactOperator γ) (h319 : Cond319 C φ) :
    (Gamma C K T φ J γ π f).Nonempty ∧ Bornology.IsBounded (Gamma C K T φ J γ π f) ∧
      IsSeqWeaklyClosed (Gamma C K T φ J γ π f) := by sorry

end QuasiHemiVI.Existence
