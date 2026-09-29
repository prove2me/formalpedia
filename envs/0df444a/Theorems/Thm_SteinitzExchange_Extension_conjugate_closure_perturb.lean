-- Prove2me | Theorems.Thm_SteinitzExchange_Extension_conjugate_closure_perturb
-- name    : SteinitzExchange.Extension.conjugate_closure_perturb
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:44:44.65276+00:00
-- url     : https://prove2.me/theorems/68ebcf4c-841e-4c5c-bf9a-cbc8ee89a126
-- title:
--   Lemma 4.2 — conjugate and concave closure under linear perturbation
-- statement:
--   Let $B\subseteq\mathbb Z^V$ be a nonempty finite set, $g:B\to\mathbb R$ and $p_0:V\to\mathbb R$, and let $g[p_0](x)=g(x)+\langle p_0,x\rangle$. Then
--
--   1. $(g[p_0])^\circ(p)=g^\circ(p-p_0)$ for every $p\in\mathbb R^V$;
--   2. $(g[p_0])^\wedge(b)=\hat g[p_0](b)=\hat g(b)+\langle p_0,b\rangle$ for every $b\in\overline B$,
--
--   where $(g[p_0])^\wedge$ is the concave closure of $g[p_0]$.
--
--   Part (2) says that taking the concave closure commutes with adding a linear function, which is how argmax statements for $\omega[p]$ are moved between $B$ and $\overline B$.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 285, Lemma 4.2, Eq. (4.7)

import Mathlib
import Definitions.Def_SteinitzExchange_Extension_IntegralBaseSet
import Definitions.Def_SteinitzExchange_Extension_Exchange
import Definitions.Def_SteinitzExchange_Extension_ConcaveClosure

namespace SteinitzExchange.Extension

/-- Murota 1996, p. 285, Lemma 4.2, for any `g : B → ℝ` on a nonempty finite `B ⊆ ℤ^V`:
(1) `(g[p₀])°(p) = g°(p − p₀)`;
(2) `(g[p₀])^(b) = ĝ[p₀](b) = ĝ(b) + ⟨p₀, b⟩` for `b ∈ B̄`. -/
theorem conjugate_closure_perturb {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Finset (V → ℤ)) (hB : B.Nonempty) (g : (V → ℤ) → ℝ) (p₀ : V → ℝ) :
    (∀ p : V → ℝ, concaveConj B (perturb g p₀) p = concaveConj B g (p - p₀)) ∧
    (∀ b ∈ hull B, concaveClosure B (perturb g p₀) b = concaveClosure B g b + pairing p₀ b) := by sorry

end SteinitzExchange.Extension
