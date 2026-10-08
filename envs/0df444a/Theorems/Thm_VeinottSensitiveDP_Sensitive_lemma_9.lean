-- Prove2me | Theorems.Thm_VeinottSensitiveDP_Sensitive_lemma_9
-- name    : VeinottSensitiveDP.Sensitive.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:56:08.084401+00:00
-- url     : https://prove2.me/theorems/0d4000fb-f028-41cf-9234-5eb28c78b30a
-- title:
--   Lemma 9 — y_n^±(g) − y_n^±(f) = ±P*(g)ψ_{n+1}^± + Σ_{k=0}^{n+1} (∓1)^k H(g)^{k+1} ψ_{n−k}^±
-- statement:
--   In the model of §4, for all $f,g\in F$ and $n=-2,-1,0,\dots$,
--   $$y_n^\pm(g)-y_n^\pm(f)=\pm P^*(g)\,\psi_{n+1}^\pm(g,f)+\sum_{k=0}^{n+1}(\mp1)^kH(g)^{k+1}\,\psi_{n-k}^\pm(g,f).$$
--
--   The identity expresses the change in the Laurent coefficients caused by switching from $f$ to $g$ through the test quantities $\psi^\pm(g,f)$; in particular $\Psi_{n+1}^\pm(g,f)=0$ forces $Y_n^\pm(g)=Y_n^\pm(f)$.
--
--   **Formalization Note** The two signs $\pm$ are one real parameter $\sigma\in\{1,-1\}$: $\sigma=1$ is $+$ and $\sigma=-1$ is $-$. For $n=-2$ the sum is empty. No spectral hypothesis is needed.
-- source:
--   Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria, Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1648, §4, Lemma 9

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_VeinottSensitiveDP_Sensitive_Matrix
import Definitions.Def_VeinottSensitiveDP_Sensitive_Model
import Definitions.Def_VeinottSensitiveDP_Sensitive_Optimality
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottSensitiveDP.Sensitive

/-- Lemma 9: if `f, g ε F`, then for `n = −2, −1, 0, ⋯`
`y_n^±(g) − y_n^±(f) = ±P*(g)ψ_{n+1}^±(g, f) + Σ_{k=0}^{n+1} (∓1)^k H(g)^{k+1} ψ_{n−k}^±(g, f)`.

Veinott, Discrete Dynamic Programming with Sensitive Discount Optimality Criteria,
Ann. Math. Statist. 40(5):1635–1660 (1969), DOI 10.1214/aoms/1177697379, p. 1648, §4, Lemma 9.

**Formalization Note.** `σ = 1` is the sign `+` and `σ = −1` the sign `−`; `∓1 = −σ`. The sum over `k = 0, …, n + 1` is
`Finset.range (n + 2).toNat` (empty for `n = −2`); every index `n − k` is `≧ −1`. No spectral
hypothesis is needed. -/
theorem lemma_9 {St : Type} [Fintype St] [DecidableEq St] [Nonempty St]
    {A : St → Type} [∀ s, Fintype (A s)] [∀ s, DecidableEq (A s)] [∀ s, Nonempty (A s)]
    (M : Model St A)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (f g : DecisionRule A) (n : ℤ) (hn : -2 ≤ n) :
    M.y σ g n - M.y σ f n =
      σ • (M.Pstar g *ᵥ M.ψ σ g f (n + 1)) +
        ∑ k ∈ Finset.range (n + 2).toNat,
          (-σ) ^ k • (M.H g ^ (k + 1) *ᵥ M.ψ σ g f (n - k)) := by sorry

end VeinottSensitiveDP.Sensitive
