-- Prove2me | Theorems.Thm_ProxBundle_GPB_Supplement_lemma_5_1
-- name    : ProxBundle.GPB.Supplement.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:35:31.569824+00:00
-- url     : https://prove2.me/theorems/4babf6c2-56d8-407e-8ccd-e2d758d46f54
-- title:
--   Lemma 5.1 — accepted coefficients and cycle contraction
-- statement:
--   Let $f+h$ satisfy (A1)–(A3) with nonnegative $M_f,L_f,\mu$, a nonempty optimal set, and the minimizing pair of (9). For every operational 1C-APB run with $x_0\in D$, $\lambda,\varepsilon>0$ and $\beta\ge1$, both assertions hold:
--
--   1. For every accepted index $j\ge0$,
--   $$0\le\tau_j\le(1+\bar\tau)/2.$$
--   2. For any consecutive serious indices $a<b$, the terminal gap obeys $t_b\le\varepsilon/2$, and every index $a+1<j\le b$ in that cycle satisfies
--   $$t_j-\varepsilon/4\le\tau_j(t_{j-1}-\varepsilon/4).$$
--
--   Here $\bar\tau=8\lambda_\mu T_\varepsilon^2/(\varepsilon+8\lambda_\mu T_\varepsilon^2)$, including zero when $T_\varepsilon^2=0$. These two clauses supply the coefficient invariant and shifted-gap estimate used for the adaptive iteration bound.
--
--   **Formalization Note** The run predicate records trials, updates, rejection and acceptance, not these conclusions. Cycles use consecutive serious endpoints; $a=0$ is permitted. The source's assertion in the proof that later coefficients stabilize is not part of the lemma and is not asserted: for $\beta>1$ accepted coefficients can decrease. The published model's domain-relative convention and omitted lower semicontinuity of $f$ are retained. There is no positive-scale, positive-$\mu$, or $\beta=1$ restriction.
--
--   Differences from the source:
--   - generalization: The source assumes lower semicontinuity of f and uses an oracle on its extended domain. → The published domain-relative model retains the oracle inequality only on D and omits lower semicontinuity of f.; reason: Every oracle comparison in these results lies in D; the omitted regularity is not used. The immutable model is reused.
--   - encoding: The paper gives trial steps 0–4 and cycles indexed by consecutive serious iterations. → Finite trial histories and endpoint-defined cycles encode those operations, with j=0 in the coefficient invariant.; reason: Acceptance is operational; the invariant is not assumed. All beta>=1 are allowed; no false stabilization claim from the proof is added.
--   - reading: The reciprocal expression (67) is undefined at T_epsilon²=0. → tauBar is the equivalent rational expression, equal to zero there.; reason: The continuous extension keeps the affine-oracle case in the full adaptive domain.
-- source:
--   Liang & Monteiro, arXiv:2110.01084v3, p. 20, Lemma 5.1(a,b); p. 19, 1C-APB, (67)–(68)

import Mathlib
import Definitions.Def_ProxBundle_GPB_Model
import Definitions.Def_ProxBundle_GPB_Supplement_Adaptive

namespace ProxBundle.GPB.Supplement

/-- Lemma 5.1(a,b), including j=0 and every beta >= 1. -/
theorem lemma_5_1 {n : ℕ} (P : Instance n) (μ Mf Lf Mbar Lbar lam ε β : ℝ)
    (x0 : E n) (A : APBRun n)
    (hμ : 0 ≤ μ) (hMf : 0 ≤ Mf) (hLf : 0 ≤ Lf)
    (hA1 : P.A1 μ) (hA3 : P.A3 Mf Lf)
    (hmin : P.IsMinPair ε Mbar Lbar)
    (hopt : ∃ x : E n, P.IsOpt x) (hx0 : x0 ∈ P.D)
    (hlam : 0 < lam) (hε : 0 < ε) (hβ : 1 ≤ β)
    (hrun : IsAPBRun P lam ε β x0 A) :
    (∀ j : ℕ, 0 ≤ A.τ j ∧ A.τ j ≤ (1 + tauBar μ lam ε Mbar Lbar) / 2) ∧
    (∀ a b : ℕ, IsCycle P A.accepted lam ε a b →
      A.accepted.t P lam b ≤ ε / 2 ∧
        ∀ j : ℕ, a + 1 < j → j ≤ b →
          A.accepted.t P lam j - ε / 4 ≤
            A.τ j * (A.accepted.t P lam (j - 1) - ε / 4)) := by sorry

end ProxBundle.GPB.Supplement
