-- Prove2me | Theorems.Thm_Rank2Sha_curve389a1_tameDiscriminant_ne_zero
-- name    : Rank2Sha.curve389a1_tameDiscriminant_ne_zero
-- status  : Open
-- author  : @barindersbanwait
-- created : 2026-11-26T14:27:38.046942+00:00
-- url     : https://prove2.me/theorems/b033e495-f56d-5f4a-9e41-21eb60e3f48a
-- title:
--   Kolyvagin primes for 389a1 with nonzero tame discriminant (CHEB′)
-- statement:
--   Let $E$ be the elliptic curve $y^2 + y = x^3 + x^2 - 2x$ over $\mathbb{Q}$ (LMFDB 389.a1), with the basis $P_1 = (0,0)$, $P_2 = (-1,1)$ of $E(\mathbb{Q})$. For a prime $p$, a **Kolyvagin prime** for $p$ is a prime $l \ne 389$ with $l \equiv 1 \pmod p$ such that $E(\mathbb{F}_l)[p]$ is cyclic of order $p$.
--
--   For distinct Kolyvagin primes $l_1, l_2$ for $p$, the **tame discriminant** is
--
--   $$
--   M(l_1, l_2) = h_{l_1}(P_1,P_1)\,h_{l_2}(P_2,P_2) + h_{l_1}(P_2,P_2)\,h_{l_2}(P_1,P_1) - 2\,h_{l_1}(P_1,P_2)\,h_{l_2}(P_1,P_2) \in \mathbb{F}_p ,
--   $$
--
--   where $h_l(P,Q) = \lambda_l\big(\tau_l((\#E(\mathbb{F}_l)/p)\,\bar P, \bar Q)\big)$, $\tau_l$ is the Tate–Lichtenbaum pairing $E(\mathbb{F}_l)[p] \times E(\mathbb{F}_l)/p \to \mathbb{F}_l^\times/(\mathbb{F}_l^\times)^p$, and $\lambda_l$ is the discrete logarithm modulo $l$ to the least primitive root, reduced modulo $p$.
--
--   The statement: for every prime $p \ge 5$ with $p \ne 389$ there are distinct Kolyvagin primes $l_1, l_2$ for $p$ with
--
--   $$
--   M(l_1, l_2) \ne 0 \quad \text{in } \mathbb{F}_p .
--   $$
--
--   Status: refereed, not formalized. A written argument derives it from Mazur and Rubin, *Kolyvagin systems*, Proposition 3.6.2(i) and Lemma 6.2.3, and the perfectness of the Tate–Lichtenbaum pairing over finite fields (Bruin, Theorem 4.1); two independent referee passes (2026-11-25) found it correct with corrections. The argument uses that $E(\mathbb{Q}) \cong \mathbb{Z}^2$, that $p$ is a prime of good reduction, and that the $p$-adic representation of $E$ is surjective, which holds for 389a1 at every $p \ge 5$.
--
--   With the identity $\delta_{l_1l_2} = M(l_1,l_2)$ for almost all $p$ (`Rank2Sha.curve389a1_kurihara_mazurTate`) it gives a nonzero Kurihara number at almost every $p$ (`Rank2Sha.curve389a1_kuriharaNumber_ne_zero`).
--
--   **Formalization Note** Primality of $p$ is an instance argument `[Fact p.Prime]`; the primality of $l_1, l_2$ is part of the existential, as witnesses of type `Fact _.Prime`. The objects are those of the definition `Rank2Sha_Kurihara389`; their agreement with the objects of the literature is a computation recorded in the definitions `Rank2Sha_PlusSymbol389` and `Rank2Sha_TatePairing`.
-- source:
--   B. Mazur, K. Rubin, Kolyvagin systems, Mem. Amer. Math. Soc. 168 (2004), no. 799, Proposition 3.6.2(i) and Lemma 6.2.3 ; P. Bruin, The Tate pairing for abelian varieties over finite fields, J. Théor. Nombres Bordeaux 23 (2011), 323-328, Theorem 4.1

import Mathlib
import Definitions.Def_Rank2Sha_Kurihara389

namespace Rank2Sha
theorem curve389a1_tameDiscriminant_ne_zero :
    ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → p ≠ 389 →
      ∃ (l₁ l₂ : ℕ) (_ : Fact l₁.Prime) (_ : Fact l₂.Prime), l₁ ≠ l₂ ∧
        IsKolyvaginPrime p l₁ ∧ IsKolyvaginPrime p l₂ ∧
          tameDiscriminant389 p l₁ l₂ ≠ 0 := by sorry
end Rank2Sha
