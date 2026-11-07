-- Prove2me | Theorems.Thm_SetMultCost_theorem_3_5
-- name    : SetMultCost.theorem_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:09.215219+00:00
-- url     : https://prove2.me/theorems/cdec262f-7f94-4078-8292-1ba4d4f86555
-- title:
--   Theorem 3.5 — set-multilinearization over small characteristic
-- statement:
--   Let $F$ be a field of characteristic $p$ and $\Delta\in\mathbb N$, and let $\mathbf r=(p,\infty,p,\infty,\dots)$. Suppose $P$ is set-multilinear of degree $d$ with respect to a partition of the variables into $d\ge1$ parts, computed by a circuit of product-depth at most $\Delta$ and size $s$. Then $P$ is computed by a set-multilinear $\mathbf r$-restricted circuit of product-depth at most $2\Delta$ and size at most
--
--   $$\big(d^d(s+1)\big)^K,$$
--
--   where $K$ depends only on $\Delta$.
--
--   The input circuit need not be homogeneous or set-multilinear. This is how lower bounds for restricted set-multilinear circuits pass to general circuits, with the alternate layers of small fan-in that characteristic $p$ provides.
--
--   Differences from the source:
--   - generalization: "P can be computed by a r-restricted product-depth-2∆ circuit" → the circuit is also set-multilinear; reason: the text after Theorem 3.1, the sentence before this theorem and the proof of Theorem 1.2 all have it; the printed conclusion omits the word
--   - reading: poly(d^d, s) → (d^d·(s+1))^K with K depending only on Δ, chosen before F and p; reason: the p² of Theorem 1.2 needs uniformity in p, and Δ is constant
--   - encoding: product-height in layered circuits → an existential height function; reason: layer heights are one such function
-- source:
--   Behera, Forbes, Saptharishi, Tavenas, On the Cost of Set-Multilinearisation in Positive Characteristic, STOC 2027 submission (manuscript sha256 841308db…), Theorem 3.5, p.12; proof of Theorem 1.2, p.25

import Mathlib
import Definitions.Def_SetMultCost_Circuit
import Definitions.Def_SetMultCost_Circuit_HasProductDepthLE
import Definitions.Def_SetMultCost_Circuit_IsRestricted
import Definitions.Def_SetMultCost_IsSetMultilinearOn
import Definitions.Def_SetMultCost_Circuit_IsSetMultilinear

universe u v

namespace SetMultCost

/-- **Theorem 3.5 (Set-Multilinearization over small characteristic).** Behera, Forbes, Saptharishi, Tavenas, *On the Cost of Set-Multilinearisation in Positive
Characteristic*, STOC 2027 submission (manuscript sha256 841308db…), p.12: "Let F be any
field with char(F) = p and ∆ ∈ N denote the product-depth parameter. The following holds over F. Let
r = (p, ∞, p, ∞, . . .) ∈ (p, ∞)^{2∆}. Suppose P(x) is a set-multilinear polynomial of degree-d that
can be computed by a product-depth-∆ circuit of size s. Then P can be computed by a r-restricted
product-depth-2∆ circuit of size poly(d^d, s)."

**Formalization Note.** A printed omission: the conclusion says "r-restricted" without
"set-multilinear", while the text after Theorem 3.1, the sentence before this theorem, and the proof
of Theorem 1.2 (p.25, "Φ′ is a … restricted product-depth 2∆ set-multilinear circuit") have it, so it
is stated. `poly(d^d, s)` is `(d^d · (s + 1))^K` with `K` depending only on `Δ`, chosen before the
field and `p`, since the `p²` of Theorem 1.2 needs uniformity in `p`. -/
theorem theorem_3_5 (Δ : ℕ) :
    ∃ K : ℕ, ∀ (F : Type u) [Field F] (p : ℕ), p.Prime → ∀ [CharP F p] (d : ℕ), 1 ≤ d →
      ∀ (σ : Type v) (part : σ → Fin d) (Φ : Circuit σ F),
        IsSetMultilinearOn part Finset.univ Φ.value → Φ.HasProductDepthLE Δ →
        ∃ Φ' : Circuit σ F, Φ'.value = Φ.value ∧ Φ'.IsSetMultilinear part ∧
          Φ'.IsRestricted (2 * Δ) (altRestriction p) ∧
          Φ'.size ≤ (d ^ d * (Φ.size + 1)) ^ K := by sorry

end SetMultCost
