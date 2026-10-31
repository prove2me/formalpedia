-- Prove2me | Theorems.Thm_RobustPrefLearn_MTP_theorem_4
-- name    : RobustPrefLearn.MTP.theorem_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:36:10.94672+00:00
-- url     : https://prove2.me/theorems/c3b19632-098e-44cf-b9da-04827362839b
-- title:
--   Theorem 4, p. 17 — 𝔞_n, 𝔟_n, λ*_n > 0, and λ^OA_* of (7) is the unique optimal display distribution of (5)
-- statement:
--   Throughout, $K\ge2$ versions and $0<p<1$. Let $f^{\mathrm{OA}}_*=f^{\mathrm{OA}}_{\sigma_*}$ for the identity ranking $\sigma_*$. The numbers $\mathfrak a_n$, $\mathfrak b_n$ and $\lambda^*_n$ ($n=2,\dots,K$) of (6) are positive, $\lambda^{\mathrm{OA}}_*$ of (7) is a probability distribution on $\mathcal S$, and it is the unique optimal solution of the outer maximization in
--   $$\max_{\lambda\in\Delta(\mathcal S)}\ \min_{\bar f\in\overline{\mathcal M}_p(f^{\mathrm{OA}}_*)} D_\lambda(f^{\mathrm{OA}}_*\|\bar f). \tag{5}$$
--
--   The optimal display rule is static, supported on the $K-1$ nested sets $[2],\dots,[K]$; the Myopic Tracking Policy uses it at every step.
--
--   **Formalization Note** Versions $1,\dots,K$ are `Fin K` (version $m$ is `⟨m-1, _⟩`), and a ranking `σ : Equiv.Perm (Fin K)` sends a version to its rank **0-based**, so `σ X = 0` is the paper's $\sigma(X)=1$. The inner minimum is the infimum in $[0,\infty]$ over all of $\overline{\mathcal M}_p(f^{\mathrm{OA}}_*)$, as printed. Optimality is $g(\lambda)\le g(\lambda^{\mathrm{OA}}_*)$ for every $\lambda\in\Delta(\mathcal S)$, and uniqueness is that $g(\lambda)=g(\lambda^{\mathrm{OA}}_*)$ forces $\lambda=\lambda^{\mathrm{OA}}_*$. The hypotheses $K\ge2$ ("$K\ge2$ available alternatives", §3) and $0<p<1$ are added: Definition 1 allows $p=0$, but then $\mathcal M_0$ is empty and $\log(1/p)$ is undefined.
-- source:
--   Feng, Caldentey & Ryan, Robust Learning of Consumer Preferences, SSRN 3215614 (https://ssrn.com/abstract=3215614), p. 17, Theorem 4, (5)–(7)

import Mathlib
import Definitions.Def_RobustPrefLearn_MTP_OA

open scoped ENNReal

namespace RobustPrefLearn.MTP

/-- Theorem 4, p. 17. The numbers `𝔞_n`, `𝔟_n`, `λ*_n` (`n = 2, …, K`) of (6) are positive, and
`λ^OA_*` of (7) is the unique optimal solution of the outer maximization of (5),
`max_{λ ∈ Δ(𝒮)} min_{f̄ ∈ M̄_p(f^OA_*)} D_λ(f^OA_*‖f̄)`, where `f^OA_* = f^OA_{σ*}`. -/
theorem theorem_4 (K : ℕ) (hK : 2 ≤ K) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (∀ n ∈ Finset.Icc 2 K, 0 < aSeq p n ∧ 0 < bSeq p n ∧ 0 < lamStar K p n) ∧
    lamOA K p ∈ simplex K ∧
    (∀ lam ∈ simplex K,
      (⨅ g ∈ alt p (oa p (1 : Equiv.Perm (Fin K))),
          ENNReal.ofReal (Dlam lam (oa p (1 : Equiv.Perm (Fin K))) g)) ≤
        ⨅ g ∈ alt p (oa p (1 : Equiv.Perm (Fin K))),
          ENNReal.ofReal (Dlam (lamOA K p) (oa p (1 : Equiv.Perm (Fin K))) g)) ∧
    (∀ lam ∈ simplex K,
      (⨅ g ∈ alt p (oa p (1 : Equiv.Perm (Fin K))),
          ENNReal.ofReal (Dlam lam (oa p (1 : Equiv.Perm (Fin K))) g)) =
        (⨅ g ∈ alt p (oa p (1 : Equiv.Perm (Fin K))),
          ENNReal.ofReal (Dlam (lamOA K p) (oa p (1 : Equiv.Perm (Fin K))) g)) →
      lam = lamOA K p) := by sorry

end RobustPrefLearn.MTP
