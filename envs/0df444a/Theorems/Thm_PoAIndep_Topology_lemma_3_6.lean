-- Prove2me | Theorems.Thm_PoAIndep_Topology_lemma_3_6
-- name    : PoAIndep.Topology.lemma_3_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:22.752301+00:00
-- url     : https://prove2.me/theorems/13838d1a-0d9e-41c8-8012-d6d78f24dc3a
-- title:
--   Lemma 3.6, p. 12 — λμ + (1 − λ) ≥ 1/α(𝓛) for ℓ ∈ 𝓛, f > 0, ℓ*(λf) = ℓ(f)
-- statement:
--   Let $\mathcal L$ be a standard class of latency functions with anarchy value $\alpha(\mathcal L)\in[1,\infty]$. Let $\ell\in\mathcal L$ and $f>0$, let $\lambda\in[0,1]$ solve $\ell^*(\lambda f)=\ell(f)$, and put $\mu=\ell(\lambda f)/\ell(f)$, with $\mu=1$ if $\ell(f)=0$. Then
--   $$\lambda\mu+(1-\lambda)\ge\frac{1}{\alpha(\mathcal L)} .$$
--
--   The lemma rephrases Definitions 3.2 and 3.3; it converts the edge-wise bound of Lemma 3.5 into a comparison with the cost of the Nash flow in Theorem 3.8.
--
--   **Formalization Note.** The inequality is stated in $[0,\infty]$: the left side is $\alpha(\mathcal L)^{-1}$, which is $0$ when $\alpha(\mathcal L)=\infty$, as $1/\infty=0$ on the page.
-- source:
--   Roughgarden, The price of anarchy is independent of the network topology (journal-version manuscript, Dec. 23, 2002), p. 12, Lemma 3.6

import Mathlib
import Definitions.Def_PoAIndep_Topology_Model

namespace PoAIndep.Topology

theorem lemma_3_6 (L : Set (ℝ → ℝ)) (hL : IsStandardClass L) (ℓ : ℝ → ℝ) (hℓ : ℓ ∈ L)
    (x : ℝ) (hx : 0 < x) (lam : ℝ) (hlam : lam ∈ Set.Icc (0 : ℝ) 1)
    (hsolve : marginalCost ℓ (lam * x) = ℓ x) :
    (anarchyValue L)⁻¹ ≤
      ENNReal.ofReal (lam * (if ℓ x = 0 then 1 else ℓ (lam * x) / ℓ x) + (1 - lam)) := by sorry

end PoAIndep.Topology
