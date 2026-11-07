-- Prove2me | Theorems.Thm_QuarticGap_lemma_3_2
-- name    : QuarticGap.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:45:27.044598+00:00
-- url     : https://prove2.me/theorems/db104c2a-b84a-4247-b517-ef7bfa3d9736
-- title:
--   Lemma 3.2 — the biases $\Lambda_{\sin}$, $\Lambda_{\cos}$ and the bound $|\Phi| \le \Phi_{\max}$
-- statement:
--   Let $S$ be a set of $K \ge 1$ characters, $\gamma \in \mathbb C^S$, $\beta \in \mathbb C$, $d > 0$, and $f$ uniformly random. The biases of the sine test and of the cosine test are
--   $$
--   \Lambda_{\sin} = \frac{2b_M}{dK}\sum_{s\in S}\mathrm{Re}(\bar\gamma_s\beta), \qquad \Lambda_{\cos} = \frac{|\beta|^2(a_M-c_M)}{d} .
--   $$
--   Every Boolean function satisfies $|\Phi(f)| \le \Phi_{\max}$, where $\Phi_{\max} = 4(\|\gamma\|^2+|\beta|^2 M)/(dK)$.
--
--   The bias is the signal that an exact sampler carries and a low-query algorithm cannot reproduce.
--
--   Differences from the source:
--   - encoding: a set of K characters → a nonempty Finset S with K = S.card; reason: the source divides by K and takes log(2K); K = 0 is meaningless
--   - encoding: independent uniform signs, uniformly random f or W → the uniform distribution on the finite set of sign functions; reason: the same law
-- source:
--   Chakrabarti, Herman, Kim, Ozgul, The Quartic Gap Between Quantum and Dequantized Algorithms for Linear Algebra Is Tight, arXiv:2610.42069 (file sha256 9f68aaf9…), Lemma 3.2, p.23

import Mathlib
import Definitions.Def_QuarticGap_Phi

open QAlgorithms

namespace QuarticGap

/-- Lemma 3.2 (arXiv:2610.42069 (file sha256 9f68aaf9…), p.23). The biases of the two tests are
`Λ_sin = (2b_M/(dK)) ∑_{s∈S} Re(γ̄_s β)` and `Λ_cos = |β|²(a_M − c_M)/d`, and every Boolean function
satisfies `|Φ(f)| ≤ Φ_max`.

**Formalization Note** `K = |S| ≥ 1`: the source divides by `K`. The overline in `Re(γ̄_s β)` is on
the rendered page and is lost in the PDF's text layer. -/
theorem lemma_3_2 {m : ℕ} (hm : 2 ≤ m) (S : Finset (Qubits m)) (hS : S.Nonempty) (γ : S → ℂ) (β : ℂ)
    (d : ℝ) (hd : 0 < d) :
    Lambda .sin S γ β d =
      2 * bM m / (d * S.card) * ∑ s, ((starRingEnd ℂ) (γ s) * β).re ∧
    Lambda .cos S γ β d = ‖β‖ ^ 2 * (aM m - cM m) / d ∧
    ∀ (k : TestKind) (f : Qubits m → ℤˣ), |Phi k S γ β d f| ≤ PhiMax S γ β d := by sorry

end QuarticGap
